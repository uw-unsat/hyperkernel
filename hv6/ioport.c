#include <string.h>
#include "ioport.h"

/*
 * Map port to owner pid:
 * 0: free
 * -1: reserved by kernel
 * others: taken by pid
 */
static pid_t io_table[SZ_64K];

int sys_alloc_io_bitmap(pn_t pn1, pn_t pn2, pn_t pn3)
{
    struct proc *proc;

    if (!(pn1 + 1 == pn2 && pn2 + 1 == pn3))
        return -EINVAL;

    proc = get_proc(current);
    if (proc->use_io_bitmap)
        return -EEXIST;

    /*
     * Since svm needs 3 consecutive pages and vmx needs 2 pages,
     * we follow the more stricted (svm) rule.  Note that we use only
     * 2 pages for the I/O bitmap; as the 3rd page contains all 1s,
     * any wrap-around port access will cause vmexit on svm, which
     * matches the unconditional vmexit behavior on vmx.
     */

    if (!is_page_type(pn1, PAGE_TYPE_FREE))
        return -EINVAL;
    if (!is_page_type(pn2, PAGE_TYPE_FREE))
        return -EINVAL;
    if (!is_page_type(pn3, PAGE_TYPE_FREE))
        return -EINVAL;

    alloc_page(current, PAGE_TYPE_PROC_DATA, pn1);
    alloc_page(current, PAGE_TYPE_PROC_DATA, pn2);
    alloc_page(current, PAGE_TYPE_PROC_DATA, pn3);

    /* set all bits to 1s */
    memset(get_page(pn1), 0xff, PAGE_SIZE);
    memset(get_page(pn2), 0xff, PAGE_SIZE);
    memset(get_page(pn3), 0xff, PAGE_SIZE);

    hvm_set_io_bitmap(get_page(proc->hvm), get_page(pn1));
    proc->io_bitmap_a = pn1;
    proc->io_bitmap_b = pn2;
    proc->use_io_bitmap = 1;
    return 0;
}

int sys_alloc_port(uint16_t port)
{
    struct proc *proc;

    if (io_table[port])
        return -EBUSY;

    proc = get_proc(current);
    if (!proc->use_io_bitmap)
        return -EACCES;

    io_table[port] = current;
    if (port < 0x8000)
        bit_clear(port, get_page(proc->io_bitmap_a));
    else
        bit_clear(port - 0x8000, get_page(proc->io_bitmap_b));
    ++proc->nr_ports;
    return 0;
}

int sys_reclaim_port(uint16_t port)
{
    pid_t pid = io_table[port];

    if (!is_proc_state(pid, PROC_ZOMBIE))
        return -EACCES;

    io_table[port] = 0;
    /* no need to clear per-process I/O bitmap */
    --get_proc(pid)->nr_ports;
    return 0;
}

void reserve_port(uint16_t port)
{
    /* set owner to pid -1 so it cannot be allocated */
    io_table[port] = ~(pid_t)0;
}

void reserve_ports(uint16_t port, size_t n)
{
    size_t i;

    assert(n <= SZ_64K - port, "invalid port");
    for (i = 0; i < n; ++i)
        reserve_port(port + i);
}

void allow_port(uint16_t port)
{
    assert(io_table[port], "port already taken");
    io_table[port] = 0;
}

void allow_ports(uint16_t port, size_t n)
{
    size_t i;

    assert(n <= SZ_64K - port, "invalid port");
    for (i = 0; i < n; ++i)
        allow_port(port + i);
}
