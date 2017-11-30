#pragma once

#include <hvm.h>
#include "fd.h"
#include "vm.h"

extern struct proc proc_table[NPROC];

extern pid_t current;

int alloc_proc(pid_t pid, pn_t page_table_root, pn_t stack, pn_t hvm);
noreturn void run_current(void);

/* defined in entry.S */
int sys_clone(pid_t pid, pn_t pml4, pn_t stack, pn_t hvm);
int sys_set_proc_name(uint64_t name0, uint64_t name1);
int sys_set_runnable(pid_t pid);
/* defined in entry.S */
int sys_switch(pid_t pid);
int sys_kill(pid_t pid);
int sys_reap(pid_t pid);
int sys_reparent(pid_t pid);

void preempt(void);
void fault(void);

static struct proc *get_proc(pid_t pid)
{
    assert(is_pid_valid(pid), "pid must be valid");
    return &proc_table[pid];
}

static inline bool is_proc_state(pid_t pid, enum proc_state state)
{
    return is_pid_valid(pid) && get_proc(pid)->state == state;
}

/* permission check: we allow a pid to modify itself or its embryo */
static inline bool is_current_or_embryo(pid_t pid)
{
    struct proc *proc;

    if (pid == current)
        return true;
    proc = get_proc(pid);
    if (proc->ppid == current && proc->state == PROC_EMBRYO)
        return true;
    return false;
}

static inline fn_t get_fd(pid_t pid, int fd)
{
    assert(is_fd_valid(fd), "fd must be valid");
    return get_proc(pid)->ofile[fd];
}

static inline bool is_fd_empty(pid_t pid, int fd)
{
    return is_fd_valid(fd) && is_fn_valid(get_fd(pid, fd));
}

static inline void set_fd(pid_t pid, int fd, fn_t fn)
{
    struct proc *proc;
    struct file *file;

    assert(get_fd(pid, fd) == 0, "fd must be valid");
    proc = get_proc(pid);
    file = get_file(fn);
    proc->ofile[fd] = fn;
    ++proc->nr_fds;
    ++file->refcnt;
}

static inline void proc_ready_add(struct proc *proc)
{
    FREELIST_ADD_TAIL(proc_table, ready, proc - proc_table, current);
}

static inline void proc_ready_del(struct proc *proc)
{
    FREELIST_DEL(proc_table, ready, proc - proc_table);
}
