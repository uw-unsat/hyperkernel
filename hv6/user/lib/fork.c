#include "user.h"

static void dup_pt(pid_t pid, pn_t pt, size_t n)
{
    size_t i;
    int r;

    for (i = 0; i < PTRS_PER_PT; ++i) {
        pte_t entry, perm;
        pn_t pn, frame;
        uintptr_t va;

        entry = uvpt[n + i];
        if (!(entry & PTE_P))
            continue;
        perm = entry & PTE_PERM_MASK;
        va = (n + i) * PAGE_SIZE;
        if (va & BIT64(47))
            va |= BITMASK64(63, 48);

        if (va >= UPAGES_START && va < UPAGES_END) {
            r = sys_map_page_desc(pid, pt, i, (va - UPAGES_START) / PAGE_SIZE, perm);
            assert(r == 0, "sys_map_page_desc");
            continue;
        }

        if (va >= UPROCS_START && va < UPROCS_END) {
            r = sys_map_proc(pid, pt, i, (va - UPROCS_START) / PAGE_SIZE, perm);
            assert(r == 0, "sys_map_proc");
            continue;
        }

        if (va >= UDEVS_START && va < UDEVS_END) {
            r = sys_map_dev(pid, pt, i, (va - UDEVS_START) / PAGE_SIZE, perm);
            assert(r == 0, "sys_map_dev");
            continue;
        }

        if (va >= UFILES_START && va < UFILES_END) {
            r = sys_map_file(pid, pt, i, (va - UFILES_START) / PAGE_SIZE, perm);
            assert(r == 0, "sys_map_file");
            continue;
        }

        pn = phys_to_pn(PTE_ADDR(entry));
        assert(upages[pn].type == PAGE_TYPE_FRAME, "must be frame");
        frame = find_free_page();
        r = sys_alloc_frame(pid, pt, i, frame, perm);
        assert(r == 0, "sys_alloc_frame");
        r = sys_copy_frame(pn, pid, frame);
        assert(r == 0, "sys_copy_frame");
    }
}

static void dup_pd(pid_t pid, pn_t pd, size_t n)
{
    size_t i;
    int r;

    for (i = 0; i < PTRS_PER_PD; ++i) {
        pte_t entry;
        pn_t pt;

        entry = uvpd[n + i];
        if (!(entry & PTE_P))
            continue;
        pt = find_free_page();
        r = sys_alloc_pt(pid, pd, i, pt, entry & PTE_PERM_MASK);
        assert(r == 0, "sys_alloc_pt");
        dup_pt(pid, pt, (n + i) * PTRS_PER_PD);
    }
}

static void dup_pdpt(pid_t pid, pn_t pdpt, size_t n)
{
    size_t i;
    int r;

    for (i = 0; i < PTRS_PER_PDPT; ++i) {
        pte_t entry;
        pn_t pd;

        entry = uvpdpt[n + i];
        if (!(entry & PTE_P))
            continue;
        pd = find_free_page();
        r = sys_alloc_pd(pid, pdpt, i, pd, entry & PTE_PERM_MASK);
        assert(r == 0, "sys_alloc_pd");
        dup_pd(pid, pd, (n + i) * PTRS_PER_PDPT);
    }
}

static void dup_pml4(pid_t pid, pn_t pml4)
{
    register_t cr3 = rcr3();
    size_t i;
    int r;

    /* a PML4 entry is either to itself or to pdpt */
    for (i = 0; i < PTRS_PER_PML4; ++i) {
        pte_t entry, perm;
        pn_t pn, pdpt;

        entry = uvpml4[i];
        if (!(entry & PTE_P))
            continue;

        perm = entry & PTE_PERM_MASK;
        /* uvpt */
        if (PTE_ADDR(entry) == cr3) {
            assert(i == UVPML4_INDEX, "must be the uvpml4 index");
            r = sys_map_pml4(pid, i, perm);
            assert(r == 0, "sys_map_pml4");
            continue;
        }

        /* pdpt */
        pn = phys_to_pn(PTE_ADDR(entry));
        assert(upages[pn].type == PAGE_TYPE_X86_PDPT, "must be pdpt");
        pdpt = find_free_page();
        r = sys_alloc_pdpt(pid, pml4, i, pdpt, perm);
        assert(r == 0, "sys_alloc_pdpt");
        dup_pdpt(pid, pdpt, i * PTRS_PER_PML4);
    }
}

pid_t fork(void)
{
    pid_t pid;
    pn_t pml4, stack, hvm;
    int r;
    size_t i;

    /* allocate a child process */
    pid = find_free_pid();
    find_free_pages(3, &pml4, &stack, &hvm);
    r = sys_clone(pid, pml4, stack, hvm);
    assert(r == 0, "sys_clone");

    /*
     * The child process will start here as we ensure sys_clone is inlined.
     */
    if (getpid() == pid) {
        struct proc *proc = &uprocs[ucurrent->ppid];

        sys_set_proc_name(proc->name[0], proc->name[1]);
        return 0;
    }

    /* finish setting up child in parent process */

    /* copy file descriptors */
    for (i = 0; i < NOFILE; ++i) {
        if (ucurrent->ofile[i] == 0)
            continue;
        r = sys_dup(i, pid, i);
        assert(r == 0, "sys_dup");
    }

    /* copy the page table */
    dup_pml4(pid, pml4);

    /* make the child runnable */
    r = sys_set_runnable(pid);
    assert(r == 0, "sys_set_runnable");

    return pid;
}

noreturn void exit(void)
{
    int i;

    /* Do some clean-up work, which is not necessary though. */

    /* close opened files */
    for (i = 0; i < NOFILE; ++i) {
        if (ucurrent->ofile[i])
            close(i);
    }

    /* kill itself */
    sys_kill(getpid());
    /* switch out */
    while (1) {
        yield();
        pause();
    }
}

int kill(pid_t pid)
{
    if (pid == getpid())
        exit();
    return sys_kill(pid);
}

pid_t wait(void)
{
    pid_t current = getpid(), pid;
    int r;

    while (1) {
        bool has_kids = false;

        for (pid = 2; pid < NPROC; ++pid) {
            struct proc *proc = &uprocs[pid];

            if (proc->ppid != current)
                continue;
            has_kids = true;
            if (proc->state == PROC_ZOMBIE)
                goto found;
        }

        /* no child processes */
        if (!has_kids)
            return -ECHILD;

        /* yield to child processes */
        yield();
    }

found:
    if (uprocs[pid].nr_children) {
        pid_t child;

        for (child = 0; child < NPROC; ++child) {
            if (uprocs[child].ppid == pid) {
                r = sys_reparent(child);
                assert(r == 0, "sys_reparent");
            }
        }
    }
    assert(uprocs[pid].nr_children == 0, "nr_children must be zero");

    if (uprocs[pid].nr_fds) {
        int fd;

        for (fd = 0; fd < NOFILE; ++fd) {
            if (uprocs[pid].ofile[fd]) {
                r = sys_close(pid, fd);
                assert(r == 0, "sys_close");
            }
        }
    }
    assert(uprocs[pid].nr_fds == 0, "nr_fds must be zero");

    if (uprocs[pid].nr_intremaps) {
        size_t index;

        for (index = 0; index < NINTREMAP; ++index)
            sys_reclaim_intremap(index);
    }
    assert(uprocs[pid].nr_intremaps == 0, "nr_intremaps must be zero");

    if (uprocs[pid].nr_devs) {
        size_t i;

        for (i = 0; i < NPCIDEV; ++i)
            sys_reclaim_iommu_root(udevs[i].devid);
    }
    assert(uprocs[pid].nr_devs == 0, "nr_devs must be zero");

    if (uprocs[pid].nr_ports) {
        int port;

        for (port = 0; port < SZ_64K; ++port)
            sys_reclaim_port(port);
    }
    assert(uprocs[pid].nr_ports == 0, "nr_ports must be zero");

    if (uprocs[pid].nr_pages) {
        pn_t pn;

        for (pn = 0; pn < NPAGE; ++pn) {
            if (upages[pn].pid == pid) {
                r = sys_reclaim_page(pn);
                assert(r == 0, "sys_reclaim_page");
            }
        }
    }
    assert(uprocs[pid].nr_pages == 0, "nr_pages must be zero");

    if (uprocs[pid].nr_dmapages) {
        dmapn_t dmapn;

        for (dmapn = 0; dmapn < NDMAPAGE; ++dmapn)
            sys_reclaim_iommu_frame(dmapn);
    }
    assert(uprocs[pid].nr_dmapages == 0, "nr_dmapages must be zero");

    if (uprocs[pid].nr_vectors) {
        int vector;

        for (vector = 0; vector < 256; ++vector)
            sys_reclaim_vector(vector);
    }
    assert(uprocs[pid].nr_vectors == 0, "nr_vectors must be zero");

    r = sys_reap(pid);
    assert(r == 0, "sys_reap");
    return pid;
}

void yield(void)
{
    pid_t next, current;
    int r;

    current = getpid();
    next = uprocs[current].ready.next;

    r = sys_switch(next);
    assert(r == 0, "sys_switch: %s\n", strerror(r));
}
