#include "uiommu.h"

pn_t iommu_alloc_root(size_t i, uintptr_t va, int bar)
{
    struct pci_dev *dev = &udevs[i];
    size_t n;
    pn_t iommu_pml4, iommu_pdpt;
    int r;

    iommu_pml4 = find_free_page();
    r = sys_alloc_iommu_root(dev->devid, iommu_pml4);
    assert(r == 0, "sys_alloc_iommu_root: %s", strerror(r));
    iommu_pdpt = find_free_page();
    r = sys_alloc_iommu_pdpt(iommu_pml4, 0, iommu_pdpt, PTE_P | PTE_W);
    assert(r == 0, "sys_alloc_iommu_pdpt: %s", strerror(r));

    for (n = 0; n < dev->reg_size[bar]; n += PAGE_SIZE) {
        pn_t pt = page_walk(va + n);
        size_t index = PT_INDEX(va + n);
        physaddr_t addr = dev->reg_base[bar] + n;
        pte_t perm = PTE_P | PTE_W | PTE_PWT | PTE_PCD;

        r = sys_map_pcipage(pt, index, (addr - PCI_START) / PAGE_SIZE, perm);
        assert(r == 0, "sys_map_pci");
    }

    return iommu_pdpt;
}

static void iommu_map_page(pn_t root, void *p)
{
    uintptr_t va = (uintptr_t)p;
    static pn_t pd, pt_shadow[512];
    static dmapn_t dmapn;
    pn_t pt, vm_pt;
    int r;

    assert(va % PAGE_SIZE == 0, "must be page-aligned");
    assert(va < SZ_1G, "address too large for iommu");

    /* assume everything is in the lower 1G */
    if (!pd) {
        pd = find_free_page();
        r = sys_alloc_iommu_pd(root, PDPT_INDEX(va), pd, PTE_P | PTE_W);
        assert(r == 0, "sys_alloc_iommu_pd: %s", strerror(r));
    }

    /* maintain a shadow table since we cannot directly read the iommu table */
    if (!pt_shadow[PD_INDEX(va)]) {
        pt = find_free_page();
        r = sys_alloc_iommu_pt(pd, PD_INDEX(va), pt, PTE_P | PTE_W);
        assert(r == 0, "sys_alloc_iommu_pt: %s", strerror(r));
        pt_shadow[PD_INDEX(va)] = pt;
    } else {
        pt = pt_shadow[PD_INDEX(va)];
    }

    /*
     * Hack: free a page, allocate an IOMMU frame, and map it back.
     * We are just too lazy to decide the va for IOMMU frames.
     */
    vm_pt = page_walk(va);
    r = sys_free_frame(vm_pt, PT_INDEX(va), virt_to_pn(p));
    assert(r == 0, "sys_free_frame: %s", strerror(r));
    while (1) {
        r = sys_alloc_iommu_frame(pt, PT_INDEX(va), dmapn, PTE_P | PTE_W);
        /*
         * Try to find an empty IOMMU frame by simply enumerating
         * since the metadata is not mapped to user space yet.
         */
        if (r == -EBUSY) {
            ++dmapn;
            continue;
        }
        assert(r == 0, "sys_alloc_iommu_frame: %s", strerror(r));
        break;
    }
    r = sys_map_iommu_frame(vm_pt, PT_INDEX(va), dmapn, PTE_P | PTE_W | PTE_PWT | PTE_PCD);
    assert(r == 0, "sys_map_iommu_frame: %s", strerror(r));
    /* we don't have an allocator for IOMMU frame for now */
    ++dmapn;
}

void iommu_map(pn_t root, void *va, size_t n)
{
    size_t i;

    for (i = 0; i < n; i += PAGE_SIZE)
        iommu_map_page(root, va + i);
}
