#include "mmap.h"
#include "proc.h"
#include "vm.h"

static int walk(pn_t pn, size_t index, pn_t *outpn)
{
    pte_t *entries, pte;

    entries = get_page(pn);
    pte = entries[index];
    if (!pte_valid(pte)) {
        *outpn = page_desc_table[0].link.next;
        return -ENOENT;
    }

    /* invariant: pfn here must be a valid pn */
    *outpn = pfn_to_pn(PTE_ADDR(pte) / PAGE_SIZE);
    return 0;
}

int sys_mmap_page(uintptr_t va, pte_t perm)
{
    pid_t pid = current;
    size_t index;
    pn_t pml4, pdpt, pd, pt, frame;
    int r;

    pml4 = get_proc(pid)->page_table_root;

    index = PML4_INDEX(va);
    if (walk(pml4, index, &pdpt)) {
        r = sys_alloc_pdpt(pid, pml4, index, pdpt, PTE_P|PTE_W);
        if (r)
            return r;
    }

    index = PDPT_INDEX(va);
    if (walk(pdpt, index, &pd)) {
        r = sys_alloc_pd(pid, pdpt, index, pd, PTE_P|PTE_W);
        if (r)
            return r;
    }

    index = PD_INDEX(va);
    if (walk(pd, index, &pt)) {
        r = sys_alloc_pd(pid, pd, index, pt, PTE_P|PTE_W);
        if (r)
            return r;
    }

    index = PT_INDEX(va);
    if (walk(pt, index, &frame)) {
        r = sys_alloc_frame(pid, pt, index, frame, perm);
        return r;
    }

    /* map_page() returns -EINVAL if the entry exists */
    return -EINVAL;
}

int sys_munmap_page(uintptr_t va)
{
    pn_t pml4, pdpt, pd, pt, frame;
    size_t index;

    pml4 = get_proc(current)->page_table_root;

    if (walk(pml4, PML4_INDEX(va), &pdpt))
        goto notfound;

    if (walk(pdpt, PDPT_INDEX(va), &pd))
        goto notfound;

    if (walk(pd, PD_INDEX(va), &pt))
        goto notfound;

    index = PT_INDEX(va);
    if (walk(pt, index, &frame))
        goto notfound;

    return sys_free_frame(pt, index, frame);

notfound:
    return -EINVAL;
}
