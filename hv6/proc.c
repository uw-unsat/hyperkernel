/*
 * Copyright 2017 Hyperkernel Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <uapi/machine/trap.h>
#include <string.h>
#include <time.h>
#include "proc.h"

struct proc proc_table[NPROC] __aligned(PAGE_SIZE);

pid_t current;

int alloc_proc(pid_t pid, pn_t page_table_root, pn_t stack, pn_t hvm)
{
    struct proc *proc, *parent;

    if (!is_proc_state(pid, PROC_UNUSED))
        return -ENOMEM;
    if (!is_page_type(page_table_root, PAGE_TYPE_FREE))
        return -ENOMEM;
    if (!is_page_type(stack, PAGE_TYPE_FREE))
        return -ENOMEM;
    if (!is_page_type(hvm, PAGE_TYPE_FREE))
        return -ENOMEM;
    if (page_table_root == stack)
        return -EINVAL;
    if (page_table_root == hvm)
        return -EINVAL;
    if (stack == hvm)
        return -EINVAL;

    proc = get_proc(pid);
    bzero(proc, sizeof(*proc));
    proc->ppid = current;
    proc->state = PROC_EMBRYO;

    alloc_page(pid, PAGE_TYPE_X86_PML4, page_table_root);
    proc->page_table_root = page_table_root;

    alloc_page(pid, PAGE_TYPE_PROC_DATA, stack);
    proc->stack = stack;

    alloc_page(pid, PAGE_TYPE_PROC_DATA, hvm);
    proc->hvm = hvm;

    parent = get_proc(current);
    ++parent->nr_children;

    return 0;
}

static void free_proc(pid_t pid)
{
    struct proc *proc;

    proc = get_proc(pid);
    /* init cannot be freed, so ppid should be non-zero */
    --get_proc(proc->ppid)->nr_children;

    proc->state = PROC_UNUSED;
    proc->ppid = 0;
    proc->page_table_root = 0;
    proc->stack = 0;
    proc->hvm = 0;
    proc->launched = 0;
    proc->killed = 0;
    proc->use_io_bitmap = 0;
    proc->io_bitmap_a = 0;
    proc->io_bitmap_b = 0;
    proc->name[0] = 0;
    proc->name[1] = 0;
}

/* called in entry.S */
void flush_current(void)
{
    struct proc *proc;
    void *hvm;

    proc = get_proc(current);
    hvm = get_page(proc->hvm);
    hvm_flush(hvm);
    proc->launched = 0;
}

/*
 * This is called by sys_clone in entry.S.
 * - Upon entry, current's hvm is already flushed.
 * - Upon exit, run_current() is called to return to user space.
 */
int clone_proc(pid_t pid, pn_t pml4, pn_t stack, pn_t hvm)
{
    int r;
    struct proc *proc;
    void *parent_hvm, *child_hvm;

    r = alloc_proc(pid, pml4, stack, hvm);
    if (r)
        return r;

    proc = get_proc(current);

    /* copy the kernel stack (saved registers) */
    memcpy(get_page(stack), get_page(proc->stack), PAGE_SIZE);

    parent_hvm = get_page(proc->hvm);
    child_hvm = get_page(hvm);
    /* copy hvm state */
    flush_current();
    hvm_flush(child_hvm);
    memcpy(child_hvm, parent_hvm, PAGE_SIZE);
    hvm_copy(child_hvm, parent_hvm, pid);

    /* will call run_current() upon return */
    return 0;
}

int switch_proc(pid_t pid)
{
    if (!is_pid_valid(pid))
        return -ESRCH;
    if (!is_proc_state(pid, PROC_RUNNABLE))
        return -EINVAL;

    if (current != pid) {
        struct proc *old, *new;

        old = get_proc(current);
        new = get_proc(pid);
        assert(new->state == PROC_RUNNABLE, "new proc must be runnable");

        if (old->state == PROC_RUNNING) {
            if (old->killed) {
                old->state = PROC_ZOMBIE;
                proc_ready_del(old);
            } else {
                old->state = PROC_RUNNABLE;
            }
        }
        new->state = PROC_RUNNING;
        current = pid;
    }

    /* will call run_current() upon return */
    return 0;
}

/*
 * Switch to the next available process in the ready list
 */
static void switch_next(void)
{
    pid_t next;
    int r;

    next = get_proc(current)->ready.next;

    if (next == 0 || (get_proc(next)->state != PROC_RUNNABLE))
        next = current;

    if (next == current)
        return;

    r = switch_proc(next);
    assert(r == 0, "switch_proc\n");
}

 /*
  * This is called by sys_switch in entry.S.
  * - Upon entry, current's hvm is already flushed.
  * - Upon exit, run_current() is called to return to user space.
  */
 int sys_switch_helper(pid_t pid)
 {
 #if ENABLED(CONFIG_PREEMPT)
     switch_next();
     return 0;
 #else
     return switch_proc(pid);
 #endif
 }

/*
 * sys_kill only sets killed to true, as the process may be running
 * either on the current cpu or on some other cpu.  The state will
 * change to ZOMBIE upon next timer/switch.
 */
int sys_kill(pid_t pid)
{
    struct proc *proc;

    if (!is_pid_valid(pid))
        return -ESRCH;
    /* can kill an embryo/runnable/running, not unused or zombie */
    if (is_proc_state(pid, PROC_UNUSED) || is_proc_state(pid, PROC_ZOMBIE))
        return -EINVAL;

    proc = get_proc(pid);
    proc->killed = 1;

    if (!is_proc_state(pid, PROC_RUNNING)) {
        proc->state = PROC_ZOMBIE;
        proc_ready_del(proc);
    }

    return 0;
}

noreturn void run_current(void)
{
    struct proc *proc;
    int launched;

    proc = get_proc(current);
    assert(proc->state == PROC_RUNNING, "current must be running");
    launched = proc->launched;
    proc->launched = 1;
    hvm_switch(get_page(proc->hvm), get_page(proc->stack) + PAGE_SIZE,
               kva2pa(get_page(proc->page_table_root)), ms_to_cycles(CONFIG_PREEMPT_TIMER),
               launched);
    __builtin_unreachable();
}

int sys_set_proc_name(uint64_t name0, uint64_t name1)
{
    struct proc *proc;

    proc = get_proc(current);
    proc->name[0] = name0;
    proc->name[1] = name1;
    return 0;
}

int sys_set_runnable(pid_t pid)
{
    struct proc *proc;

    if (!is_pid_valid(pid))
        return -ESRCH;
    proc = get_proc(pid);
    /* only the parent process can make it ready */
    if (proc->ppid != current)
        return -EACCES;
    /* can ready only an embryo process */
    if (proc->state != PROC_EMBRYO)
        return -EINVAL;

    proc->state = PROC_RUNNABLE;
    proc_ready_add(proc);
    return 0;
}

int sys_reap(pid_t pid)
{
    struct proc *proc;

    if (!is_pid_valid(pid))
        return -ESRCH;
    proc = get_proc(pid);
    /* only the parent process can reap */
    if (proc->ppid != current)
        return -EACCES;
    /* must be a zombie */
    if (proc->state != PROC_ZOMBIE)
        return -EINVAL;
    if (proc->nr_devs)
        return -ETXTBSY;
    if (proc->nr_children)
        return -ETXTBSY;
    if (proc->nr_fds)
        return -ETXTBSY;
    if (proc->nr_pages)
        return -ETXTBSY;
    if (proc->nr_dmapages)
        return -ETXTBSY;
    if (proc->nr_ports)
        return -ETXTBSY;
    if (proc->nr_vectors)
        return -ETXTBSY;
    if (proc->nr_intremaps)
        return -ETXTBSY;

    free_proc(pid);
    return 0;
}

int sys_reparent(pid_t pid)
{
    struct proc *proc;

    if (!is_pid_valid(pid))
        return -ESRCH;
    proc = get_proc(pid);
    /* the parent process must be zombie */
    if (!is_proc_state(proc->ppid, PROC_ZOMBIE))
        return -EINVAL;
    /* not sure if we need this */
    if (!is_proc_state(INITPID, PROC_RUNNABLE) && !is_proc_state(INITPID, PROC_RUNNING))
        return -EINVAL;

    ++get_proc(INITPID)->nr_children;
    --get_proc(proc->ppid)->nr_children;
    proc->ppid = INITPID;
    return 0;
}

/* this is called by timer interrupt */
void preempt(void)
{
    flush_current();
    switch_next();
    run_current();
}

void fault(void)
{
    pid_t pid = current;
    struct proc *proc;

    proc = get_proc(pid);
    proc->killed = 1;
    pr_info("fault: pid %ld killed\n", pid);
    switch_next();
    run_current();
}
