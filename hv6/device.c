#include <uapi/machine/cpufunc.h>
#include <uapi/machine/mmu.h>
#include <iommu.h>
#include <string.h>
#include "device.h"
#include "proc.h"
#include "vm.h"

/* pci hole pages: pfn -> devid */
struct pcipage_desc {
    devid_t devid;
    bool valid;
};

static struct pcipage_desc pcipages[NPCIPAGE];

/* pci devices metadata for user space; not used by kernel */
struct pci_dev devices[NPCIDEV] __aligned(PAGE_SIZE);

/* pci devid -> pid */
static pid_t pci_table[SZ_64K];

/* vector -> pid */
static pid_t vector_table[256];

static struct intremap intremap_table[NINTREMAP];

/* IOMMU frame pages */
volatile uint8_t dmapages[NDMAPAGE][PAGE_SIZE] __aligned(SZ_2M); /* 2M-aligned for PMR */
static struct page_desc dmapage_desc_table[NDMAPAGE];

static inline bool is_dmapage_type(dmapn_t dmapn, enum page_type type)
{
    return is_dmapn_valid(dmapn) && dmapage_desc_table[dmapn].type == type;
}

static inline bool is_dmapage_pid(dmapn_t dmapn, pid_t pid)
{
    return is_dmapn_valid(dmapn) && dmapage_desc_table[dmapn].pid == pid;
}

static int is_pcipn_valid(pn_t pcipn)
{
    return pcipn < NPCIPAGE && pcipages[pcipn].valid;
}

static pid_t pcipn_to_pid(pn_t pcipn)
{
    assert(is_pcipn_valid(pcipn), "pcipn must be valid");
    return pci_table[pcipages[pcipn].devid];
}

static int is_pcipn_pid(pn_t pcipn, pid_t pid)
{
    return is_pcipn_valid(pcipn) && pcipn_to_pid(pcipn) == pid;
}

int sys_map_pcipage(pn_t pt, size_t index, pn_t pcipn, pte_t perm)
{
    pid_t pid = current;
    pn_t pfn;

    /* check if pcipn is valid in pci pages */
    if (!is_pcipn_valid(pcipn))
        return -EINVAL;
    /* check if current owns the pcipage */
    if (!is_pcipn_pid(pcipn, pid))
        return -EACCES;

    pfn = PCI_START / PAGE_SIZE + pcipn;
    return map_page(pid, pt, index, pfn, perm, PAGE_TYPE_X86_PT);
}

static int map_iommu_page_table_page(pn_t from, size_t index, physaddr_t pa, iommu_pte_t perm,
                                     enum page_type from_type)
{
    iommu_pte_t *entries;
    uint64_t next_level = PAGE_TYPE_IOMMU_FRAME - 1 - from_type;

    if (!is_page_type(from, from_type))
        return -EINVAL;
    /* check if current owns from */
    if (!is_page_pid(from, current))
        return -EACCES;
    if (!is_page_index_valid(index))
        return -EINVAL;
    /* the same as DMAR_PTE_R | DMAR_PTE_W */
    if (perm & ~(PTE_P | PTE_W))
        return -EINVAL;

    entries = get_page(from);
    /* make sure the entry is empty */
    if (entries[index])
        return -EINVAL;

    entries[index] = iommu_entry(pa, perm, next_level);
    /* flush tlb */
    iommu_flush();
    return 0;
}

static int alloc_iommu_page_table_page(pn_t from, size_t index, pn_t to, iommu_pte_t perm,
                                       enum page_type from_type, enum page_type to_type)
{
    int r;

    if (!is_page_type(to, PAGE_TYPE_FREE))
        return -EINVAL;
    r = map_iommu_page_table_page(from, index, kva2pa(get_page(to)), perm, from_type);
    if (r)
        return r;

    alloc_page(current, to_type, to);
    return 0;
}

int sys_alloc_iommu_pdpt(pn_t from, size_t index, pn_t to, iommu_pte_t perm)
{
    int r;
    extern void iommu_hack_root(physaddr_t addr4, physaddr_t addr3);

    r = alloc_iommu_page_table_page(from, index, to, perm, PAGE_TYPE_IOMMU_PML4,
                                    PAGE_TYPE_IOMMU_PDPT);
    /* hack for qemu (3-level) */
    if (r == 0 && index == 0)
        iommu_hack_root((uintptr_t)get_page(from), (uintptr_t)get_page(to));
    return r;
}

int sys_alloc_iommu_pd(pn_t from, size_t index, pn_t to, iommu_pte_t perm)
{
    return alloc_iommu_page_table_page(from, index, to, perm, PAGE_TYPE_IOMMU_PDPT,
                                       PAGE_TYPE_IOMMU_PD);
}

int sys_alloc_iommu_pt(pn_t from, size_t index, pn_t to, iommu_pte_t perm)
{
    return alloc_iommu_page_table_page(from, index, to, perm, PAGE_TYPE_IOMMU_PD,
                                       PAGE_TYPE_IOMMU_PT);
}

int sys_alloc_iommu_frame(pn_t from, size_t index, dmapn_t to, iommu_pte_t perm)
{
    int r;
    struct page_desc *desc;

    /* check if `to' is free */
    if (!is_dmapn_valid(to))
        return -EINVAL;
    if (!is_dmapage_type(to, PAGE_TYPE_FREE))
        return -EBUSY;
    r = map_iommu_page_table_page(from, index, kva2pa(&dmapages[to]), perm, PAGE_TYPE_IOMMU_PT);
    if (r)
        return r;

    /* change the type to iommu frame */
    desc = &dmapage_desc_table[to];
    desc->type = PAGE_TYPE_IOMMU_FRAME;
    desc->pid = current;
    ++get_proc(current)->nr_dmapages;
    return 0;
}

int sys_map_iommu_frame(pn_t pt, size_t index, dmapn_t to, pte_t perm)
{
    pn_t pfn;

    /* check if `to' is an iommu frame owned by current */
    if (!is_dmapage_type(to, PAGE_TYPE_IOMMU_FRAME))
        return -EINVAL;
    if (!is_dmapage_pid(to, current))
        return -EACCES;

    pfn = (uintptr_t)dmapages / PAGE_SIZE + to;
    return map_page(current, pt, index, pfn, perm, PAGE_TYPE_X86_PT);
}

int sys_reclaim_iommu_frame(dmapn_t dmapn)
{
    struct page_desc *desc;
    pid_t pid;

    if (!is_dmapn_valid(dmapn))
        return -EINVAL;
    if (is_dmapage_type(dmapn, PAGE_TYPE_FREE))
        return -EINVAL;
    desc = &dmapage_desc_table[dmapn];
    pid = desc->pid;
    /* can reclaim pages owned by a zombie */
    if (!is_proc_state(pid, PROC_ZOMBIE))
        return -EACCES;
    /* don't reclaim anything if any device is in use */
    if (get_proc(pid)->nr_devs)
        return -EBUSY;

    desc->type = PAGE_TYPE_FREE;
    desc->pid = 0;
    --get_proc(pid)->nr_dmapages;
    return 0;
}

int sys_alloc_vector(uint8_t vector)
{
    if (vector_table[vector])
        return -EBUSY;

    vector_table[vector] = current;
    ++get_proc(current)->nr_vectors;
    return 0;
}

int sys_reclaim_vector(uint8_t vector)
{
    pid_t pid;

    pid = vector_table[vector];
    if (!is_proc_state(pid, PROC_ZOMBIE))
        return -EACCES;
    if (get_proc(pid)->nr_intremaps)
        return -EBUSY;

    vector_table[vector] = 0;
    --get_proc(pid)->nr_vectors;
    return 0;
}

void reserve_vector(uint8_t vector)
{
    /* set owner to pid -1 so it cannot be allocated */
    vector_table[vector] = ~(pid_t)0;
}

void reserve_vectors(uint8_t vector, size_t n)
{
    size_t i;

    assert(n <= 256 - vector, "invalid vector");
    for (i = 0; i < n; ++i)
        reserve_vector(vector + i);
}

static inline int is_intremap_valid(size_t index)
{
    return index < NINTREMAP;
}

static inline int is_intremap_state(size_t index, enum intremap_state state)
{
    return is_intremap_valid(index) && intremap_table[index].state == state;
}

int sys_alloc_intremap(size_t index, devid_t devid, uint8_t vector)
{
    struct intremap *ir;

    if (!is_intremap_state(index, IR_FREE))
        return -EINVAL;
    /* is the device owned by current */
    if (pci_table[devid] != current)
        return -EACCES;
    /* is the vector owned by current */
    if (vector_table[vector] != current)
        return -EACCES;

    ir = &intremap_table[index];
    ir->state = IR_ACTIVE;
    ir->devid = devid;
    ir->vector = vector;
    ++get_proc(current)->nr_intremaps;
    iommu_set_intremap(index, devid, vector);
    return 0;
}

int sys_reclaim_intremap(size_t index)
{
    struct intremap *ir;
    pid_t pid;

    if (!is_intremap_state(index, IR_ACTIVE))
        return -EINVAL;

    ir = &intremap_table[index];
    pid = pci_table[ir->devid];
    /* can only reclaim a zombie's IRTE */
    if (!is_proc_state(pid, PROC_ZOMBIE))
        return -EACCES;

    ir->state = IR_FREE;
    ir->devid = 0;
    ir->vector = 0;
    --get_proc(pid)->nr_intremaps;
    iommu_reset_intremap(index);
    return 0;
}

int sys_alloc_iommu_root(devid_t devid, pn_t pn)
{
    if (pci_table[devid])
        return -EBUSY;
    if (!is_page_type(pn, PAGE_TYPE_FREE))
        return -EINVAL;

    pci_table[devid] = current;
    alloc_page(current, PAGE_TYPE_IOMMU_PML4, pn);
    ++get_proc(current)->nr_devs;

    iommu_set_dev_root(devid, (uintptr_t)get_page(pn));
    iommu_flush();
    return 0;
}

int sys_reclaim_iommu_root(devid_t devid)
{
    pid_t pid = pci_table[devid];

    /* can free a page of a zombie process */
    if (!is_proc_state(pid, PROC_ZOMBIE))
        return -EACCES;
    if (get_proc(pid)->nr_intremaps)
        return -EBUSY;

    --get_proc(pid)->nr_devs;
    pci_table[devid] = 0;

    iommu_reset_dev_root(devid);
    iommu_flush();
    return 0;
}

int sys_ack_intr(uint8_t v)
{
    struct proc *proc = get_proc(current);

    bit_clear(v, proc->intr);
    return 0;
}

int extintr(uint8_t v)
{
    pid_t pid = vector_table[v];
    struct proc *proc;

    /* be paranoid  */
    if (!is_pid_valid(pid))
        return -EINVAL;
    proc = get_proc(pid);

    bit_set(v, proc->intr);
    /* wake up a process if a new bit is set */
    if (proc->state == PROC_SLEEPING) {
        proc->state = PROC_RUNNABLE;
        /* special value for kernel */
        proc->ipc_from = 0;
        proc->ipc_val = v;
        proc->ipc_size = 0;
    }

    return 0;
}

static void set_pcipn_owner(pn_t pn, devid_t devid)
{
    assert(pn < NPCIPAGE, "must be valid!");
    assert(!is_pcipn_valid(pn), "must be free!");

    pcipages[pn].devid = devid;
    pcipages[pn].valid = true;
}

void device_add(struct pci_func *f)
{
    static size_t nr_devices;
    struct pci_dev *dev;
    devid_t devid = f->devid;
    size_t i;

    assert(nr_devices < NPCIDEV, "too many PCI functions");
    dev = &devices[nr_devices];
    memcpy(dev, f, sizeof(struct pci_func));

    /* enable PCIe configuration space for user */
    if (pci_config_base) {
        pn_t pfn = pci_config_addr(devid) / PAGE_SIZE;

        if (!is_pfn_pcipn(pfn)) {
            pr_warn("pci: configuration address 0x%08" PRIx64 " not in the PCI region\n",
                    pfn * PAGE_SIZE);
        } else {
            set_pcipn_owner(pfn_to_pcipn(pfn), devid);
        }
    }

    for (i = 0; i < 6; ++i) {
        physaddr_t start, end;
        pn_t pfn, pfn_end;

        start = dev->reg_base[i];
        end = start + dev->reg_size[i];
        /* I/O ports */
        if (start < SZ_64K)
            continue;

        pfn = start / PAGE_SIZE;
        pfn_end = roundup(end, PAGE_SIZE) / PAGE_SIZE;
        for (; pfn < pfn_end; ++pfn) {
            if (!is_pfn_pcipn(pfn)) {
                pr_warn("pci: bar address 0x%08" PRIx64 " not in the PCI region\n", pfn * PAGE_SIZE);
                break;
            }
            set_pcipn_owner(pfn_to_pcipn(pfn), devid);
        }
    }

    nr_devices++;
}
