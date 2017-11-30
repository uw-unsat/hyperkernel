#include <uapi/machine/cpufunc.h>
#include <string.h>
#include "device.h"
#include "proc.h"
#include "vm.h"

struct page_desc page_desc_table[NPAGE] __aligned(PAGE_SIZE);
uint64_t pages[NPAGE][PAGE_SIZE / sizeof(uint64_t)] __aligned(PAGE_SIZE);

void alloc_page(pid_t pid, enum page_type type, pn_t pn)
{
    struct page_desc *desc = get_page_desc(pn);

    assert(is_page_type(pn, PAGE_TYPE_FREE), "must be a free page");
    desc->pid = pid;
    desc->type = type;

    if (pn != 0)
        FREELIST_DEL(page_desc_table, link, pn);

    bzero(get_page(pn), PAGE_SIZE);
    if (pid)
        ++get_proc(pid)->nr_pages;
}

void free_page(pn_t pn)
{
    struct page_desc *desc = get_page_desc(pn);
    pid_t pid = desc->pid;

    assert(!is_page_type(pn, PAGE_TYPE_FREE), "must not be a free page");
    desc->pid = 0;
    desc->type = PAGE_TYPE_FREE;

    if (pn != 0)
        FREELIST_ADD(page_desc_table, link, pn, 0);

    if (pid)
        --get_proc(pid)->nr_pages;
}

int map_page(pid_t pid, pn_t from_pn, size_t index, pn_t pfn, pte_t perm,
             enum page_type from_type)
{
    pte_t *entries;

    if (!is_pid_valid(pid))
        return -ESRCH;
    /* check if pid is current or its embryo */
    if (!is_current_or_embryo(pid))
        return -EACCES;
    if (!is_page_type(from_pn, from_type))
        return -EINVAL;
    /* check if pid owns from_pfn */
    if (!is_page_pid(from_pn, pid))
        return -EACCES;
    if (!is_page_index_valid(index))
        return -EINVAL;
    /* no check on pfn; left to caller */
    /* check for unsafe bits in page permissions */
    if (perm & ~PTE_PERM_MASK)
        return -EINVAL;
    /* make sure we have non-zero entries */
    if (!pte_valid(perm))
        return -EINVAL;

    entries = get_page(from_pn);
    /* make sure the entry is empty; may not be necessary but good to check */
    if (pte_valid(entries[index]))
        return -EINVAL;

    /* update the page table */
    mmio_write64(&entries[index], (pfn << PTE_PFN_SHIFT) | perm);
    hvm_invalidate_tlb(pid);
    return 0;
}

int sys_map_page_desc(pid_t pid, pn_t from, size_t index, size_t n, pte_t perm)
{
    pn_t pfn;

    if (n >= bytes_to_pages(NPAGE * sizeof(struct page_desc)))
        return -EINVAL;
    pfn = (uintptr_t)page_desc_table / PAGE_SIZE + n;
    if (pte_writable(perm))
        return -EACCES;
    return map_page(pid, from, index, pfn, perm, PAGE_TYPE_X86_PT);
}

int sys_map_pml4(pid_t pid, size_t index, pte_t perm)
{
    struct proc *proc;
    pn_t from, pfn;

    if (!is_pid_valid(pid))
        return -ESRCH;
    proc = get_proc(pid);
    from = proc->page_table_root;
    pfn = pn_to_pfn(from);
    if (pte_writable(perm))
        return -EACCES;
    return map_page(pid, from, index, pfn, perm, PAGE_TYPE_X86_PML4);
}

int sys_map_proc(pid_t pid, pn_t from, size_t index, size_t n, pte_t perm)
{
    pn_t pfn;

    if (n >= bytes_to_pages(NPROC * sizeof(struct proc)))
        return -EINVAL;
    pfn = (uintptr_t)proc_table / PAGE_SIZE + n;
    if (pte_writable(perm))
        return -EACCES;
    return map_page(pid, from, index, pfn, perm, PAGE_TYPE_X86_PT);
}

int sys_map_dev(pid_t pid, pn_t from, size_t index, size_t n, pte_t perm)
{
    pn_t pfn;

    if (n >= bytes_to_pages(NPCIDEV * sizeof(struct pci_dev)))
        return -EINVAL;
    pfn = (uintptr_t)devices / PAGE_SIZE + n;
    if (pte_writable(perm))
        return -EACCES;
    return map_page(pid, from, index, pfn, perm, PAGE_TYPE_X86_PT);
}

int sys_map_file(pid_t pid, pn_t from, size_t index, size_t n, pte_t perm)
{
    pn_t pfn;

    if (n >= bytes_to_pages(NFILE * sizeof(struct file)))
        return -EINVAL;
    pfn = (uintptr_t)file_table / PAGE_SIZE + n;
    if (pte_writable(perm))
        return -EACCES;
    return map_page(pid, from, index, pfn, perm, PAGE_TYPE_X86_PT);
}

static int alloc_page_table_page(pid_t pid, pn_t from_pn, size_t index, pn_t to_pn, pte_t perm,
                                 enum page_type from_type, enum page_type to_type)
{
    int r;
    pn_t pfn;

    if (!is_page_type(to_pn, PAGE_TYPE_FREE))
        return -EINVAL;
    pfn = pn_to_pfn(to_pn);
    r = map_page(pid, from_pn, index, pfn, perm, from_type);
    if (r)
        return r;
    /* alloc_page always succeeds so it's okay to call it after map_page */
    alloc_page(pid, to_type, to_pn);
    return 0;
}

int sys_alloc_pdpt(pid_t pid, pn_t from, size_t index, pn_t to, pte_t perm)
{
    return alloc_page_table_page(pid, from, index, to, perm, PAGE_TYPE_X86_PML4,
                                 PAGE_TYPE_X86_PDPT);
}

int sys_alloc_pd(pid_t pid, pn_t from, size_t index, pn_t to, pte_t perm)
{
    return alloc_page_table_page(pid, from, index, to, perm, PAGE_TYPE_X86_PDPT, PAGE_TYPE_X86_PD);
}

int sys_alloc_pt(pid_t pid, pn_t from, size_t index, pn_t to, pte_t perm)
{
    return alloc_page_table_page(pid, from, index, to, perm, PAGE_TYPE_X86_PD, PAGE_TYPE_X86_PT);
}

int sys_alloc_frame(pid_t pid, pn_t from, size_t index, pn_t to, pte_t perm)
{
    return alloc_page_table_page(pid, from, index, to, perm, PAGE_TYPE_X86_PT, PAGE_TYPE_FRAME);
}

/*
 * We need to_pn as a parameter; otherwise it's hard to check
 * if a given entry has a valid pn.
 */
static int free_page_table_page(pn_t from_pn, size_t index, pn_t to_pn, enum page_type from_type,
                                enum page_type to_type)
{
    pte_t *entries;

    if (!is_page_type(from_pn, from_type))
        return -EINVAL;
    if (!is_page_pid(from_pn, current))
        return -EACCES;
    if (!is_page_index_valid(index))
        return -EINVAL;
    if (!is_page_type(to_pn, to_type))
        return -EINVAL;
    if (!is_page_pid(to_pn, current))
        return -EACCES;

    entries = get_page(from_pn);
    /* check if the slot is empty */
    if (!pte_valid(entries[index]))
        return -EINVAL;
    /* check if the entry matches */
    if (pn_to_pfn(to_pn) != (PTE_ADDR(entries[index]) >> PAGE_SHIFT))
        return -EINVAL;

    /* release the next-level page */
    free_page(to_pn);
    /* wipe the entry */
    entries[index] = 0;
    hvm_invalidate_tlb(current);

    return 0;
}

int sys_free_pdpt(pn_t from, size_t index, pn_t to)
{
    return free_page_table_page(from, index, to, PAGE_TYPE_X86_PML4, PAGE_TYPE_X86_PDPT);
}

int sys_free_pd(pn_t from, size_t index, pn_t to)
{
    return free_page_table_page(from, index, to, PAGE_TYPE_X86_PDPT, PAGE_TYPE_X86_PD);
}

int sys_free_pt(pn_t from, size_t index, pn_t to)
{
    return free_page_table_page(from, index, to, PAGE_TYPE_X86_PD, PAGE_TYPE_X86_PT);
}

int sys_free_frame(pn_t from, size_t index, pn_t to)
{
    return free_page_table_page(from, index, to, PAGE_TYPE_X86_PT, PAGE_TYPE_FRAME);
}

int sys_copy_frame(pn_t from, pid_t pid, pn_t to)
{
    if (!is_page_type(from, PAGE_TYPE_FRAME))
        return -EINVAL;
    if (!is_page_pid(from, current))
        return -EACCES;
    if (!is_pid_valid(pid))
        return -ESRCH;
    if (!is_page_type(to, PAGE_TYPE_FRAME))
        return -EINVAL;
    if (!is_page_pid(to, pid))
        return -EACCES;
    if (!is_current_or_embryo(pid))
        return -EACCES;

    memcpy(get_page(to), get_page(from), PAGE_SIZE);
    return 0;
}

int sys_protect_frame(pn_t pt, size_t index, pn_t frame, pte_t perm)
{
    pte_t *entries;
    pn_t pfn;

    if (!is_page_type(pt, PAGE_TYPE_X86_PT))
        return -EINVAL;
    if (!is_page_pid(pt, current))
        return -EACCES;
    if (!is_page_index_valid(index))
        return -EINVAL;
    if (!is_page_type(frame, PAGE_TYPE_FRAME))
        return -EINVAL;
    if (!is_page_pid(frame, current))
        return -EACCES;

    entries = get_page(pt);
    /* check if the slot is empty */
    if (!pte_valid(entries[index]))
        return -EINVAL;
    /* check if the entry matches */
    pfn = PTE_ADDR(entries[index]) >> PAGE_SHIFT;
    if (pn_to_pfn(frame) != pfn)
        return -EINVAL;

    /* check for unsafe bits in page permissions */
    if (perm & ~PTE_PERM_MASK)
        return -EINVAL;
    /* make sure we have non-zero entries */
    if (!pte_valid(perm))
        return -EINVAL;

    /* update the page table */
    entries[index] = (pfn << PTE_PFN_SHIFT) | perm;
    hvm_invalidate_tlb(current);

    return 0;
}

int sys_reclaim_page(pn_t pn)
{
    struct page_desc *desc;

    if (!is_pn_valid(pn))
        return -EINVAL;
    if (is_page_type(pn, PAGE_TYPE_FREE))
        return -EINVAL;
    desc = get_page_desc(pn);
    /* can reclaim pages owned by a zombie */
    if (!is_proc_state(desc->pid, PROC_ZOMBIE))
        return -EACCES;
    /* don't reclaim anything if any device is in use */
    if (get_proc(desc->pid)->nr_devs)
        return -EBUSY;

    free_page(pn);
    return 0;
}
