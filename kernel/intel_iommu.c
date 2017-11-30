#include <uapi/machine/mmu.h>
#include <uapi/machine/cpufunc.h>
#include <uapi/pcidb.h>
#include <acpi.h>
#include <intel_iommu.h>
#include <iommu.h>
#include <string.h>
#include <symtable.h>
#include <xapic.h>

#define MAX_NR_IOMMUS	16

static struct dmar_root_entry root_table[256] __aligned(PAGE_SIZE);
static struct dmar_context_entry dev_table[SZ_64K] __aligned(PAGE_SIZE);
static struct dmar_irte ir_table[SZ_64K] __aligned(PAGE_SIZE);
static int hack_3to4;

static void *iommu_base[MAX_NR_IOMMUS];
static size_t nr_iommus;

static void intel_iommu_reset_dev_root(uint16_t id);
static void intel_iommu_set_dev_root(uint16_t id, physaddr_t addr);
static uint64_t intel_iommu_entry(uint64_t addr, uint64_t perm, uint64_t level);
static void intel_iommu_set_intremap(uint16_t index, uint16_t id, uint8_t irq);
static void intel_iommu_reset_intremap(uint16_t index);
static void intel_iommu_flush(void);
static void intel_iommu_early_set_dev_region(physaddr_t start, physaddr_t end);

/*
 * To update a bit field in this register at offset X with value of Y,
 * software must follow below steps:
 *   1. Tmp = Read GSTS_REG
 *   2. Status = (Tmp & 96FFFFFFh) // Reset the one-shot bits
 *   3. Command = (Status | (Y << X))
 *   4. Write Command to GCMD_REG
 *   5. Wait until GSTS_REG[X] indicates command is serviced.
 */
static void intel_iommu_set_gcmd(void *base, uint32_t val)
{
    uint32_t tmp, status, cmd;

    tmp = mmio_read32(base + DMAR_GSTS_REG);
    status = tmp & 0x96ffffff;
    cmd = status | val;
    mmio_write32(base + DMAR_GCMD_REG, cmd);
    while (!(mmio_read32(base + DMAR_GSTS_REG) & val))
        pause();
}

void intel_iommu_init(void)
{
    acpi_status status;
    struct acpi_table_dmar *dmar;
    struct acpi_dmar_header *hdr, *end;
    size_t i;

    status = acpi_get_table(ACPI_SIG_DMAR, 0, (struct acpi_table_header **)&dmar);
    assert(ACPI_SUCCESS(status), "DMAR not found");
    hdr = (void *)dmar + sizeof(*dmar);
    end = (void *)dmar + dmar->header.length;

    /* preallocate context tables */
    for (i = 0; i < 256; ++i)
        root_table[i].r1 = DMAR_ROOT_R1_P | (uintptr_t)(dev_table + i);

    for (; hdr < end; hdr = (void *)hdr + hdr->length) {
        struct acpi_dmar_hardware_unit *drhd;
        void *base;
        uint64_t cap, ecap;

        if (hdr->type != ACPI_DMAR_TYPE_HARDWARE_UNIT)
            continue;
        /* program IOMMUs the same way; no need to inspect device scopes */
        drhd = (void *)hdr;
        base = (void *)drhd->address;
        cap = mmio_read64(base + DMAR_CAP_REG);
        ecap = mmio_read64(base + DMAR_ECAP_REG);
        pr_info("iommu: DRHD base address 0x%016" PRIxPTR "\n", (uintptr_t)base);
        pr_info("iommu: cap 0x%016" PRIx64 " ecap 0x%016" PRIx64 "\n", cap, ecap);
        if (cap & DMAR_CAP_SAGAW_3LVL)
            pr_info("iommu: 3-level page table\n");
        if (cap & DMAR_CAP_SAGAW_4LVL)
            pr_info("iommu: 4-level page table\n");
        if (!(cap & (DMAR_CAP_SAGAW_3LVL | DMAR_CAP_SAGAW_4LVL)))
            panic("iommu: no 3-level or 4-level page-table support");
        if (!(cap & DMAR_CAP_SAGAW_4LVL))
            hack_3to4 = 1;
        if (nr_iommus >= MAX_NR_IOMMUS)
            panic("iommu: increase MAX_NR_IOMMUS");
        iommu_base[nr_iommus] = base;
        nr_iommus++;

        /* set root table */
        mmio_write64(base + DMAR_RTADDR_REG, (uintptr_t)root_table);
        intel_iommu_set_gcmd(base, DMAR_GCMD_SRTP);
        /* enable translation */
        intel_iommu_set_gcmd(base, DMAR_GCMD_TE);
        pr_info("iommu: DMA remapping enabled\n");

        if (ecap & DMAR_ECAP_IR) {
            /* set interrupt remap table pointer; x2APIC; 64K entries */
            mmio_write64(base + DMAR_IRTA_REG, (uintptr_t)ir_table | DMAR_IRTA_EIME | 0xf);
            intel_iommu_set_gcmd(base, DMAR_GCMD_SIRTP);
            /* enable interrupt remapping */
            intel_iommu_set_gcmd(base, DMAR_GCMD_IRE);
            pr_info("iommu: interrupt remapping enabled\n");
        } else {
            pr_info("iommu: no interrupt remapping\n");
        }

        if (!(cap & DMAR_CAP_PI))
            pr_info("iommu: no posted interrupts\n");
    }

    iommu_vendor = PCI_VENDOR_INTEL;
    iommu_set_dev_root = intel_iommu_set_dev_root;
    iommu_reset_dev_root = intel_iommu_reset_dev_root;
    iommu_entry = intel_iommu_entry;
    iommu_set_intremap = intel_iommu_set_intremap;
    iommu_reset_intremap = intel_iommu_reset_intremap;
    iommu_flush = intel_iommu_flush;
    iommu_early_set_dev_region = intel_iommu_early_set_dev_region;
}

static void intel_iommu_reset_dev_root(uint16_t id)
{
    /* clear P bit first */
    mmio_write64(&dev_table[id].ctx1, 0);
    mmio_write64(&dev_table[id].ctx2, 0);
    intel_iommu_flush();
}

static void intel_iommu_set_dev_root(uint16_t id, physaddr_t addr)
{
    mmio_write64(&dev_table[id].ctx2, DMAR_CTX2_AW_4LVL);
    /* set P bit last */
    mmio_write64(&dev_table[id].ctx1, DMAR_CTX1_P | addr);
    intel_iommu_flush();
}

void iommu_hack_root(physaddr_t addr4, physaddr_t addr3)
{
    size_t id;

    /* hack for qemu */
    if (!hack_3to4)
        return;
    for (id = 0; id <= SZ_64K; ++id) {
        if ((dev_table[id].ctx1 & DMAR_CTX1_ASR_MASK) == addr4)
            break;
    }
    assert(id <= SZ_64K, "4-level root not found");
    mmio_write64(&dev_table[id].ctx2, DMAR_CTX2_AW_3LVL);
    /* set P bit last */
    mmio_write64(&dev_table[id].ctx1, DMAR_CTX1_P | addr3);
    intel_iommu_flush();
}

static uint64_t intel_iommu_entry(uint64_t addr, uint64_t perm, uint64_t level)
{
    return addr | perm;
}

static void intel_iommu_set_intremap(uint16_t index, uint16_t devid, uint8_t vector)
{
    struct dmar_irte *e;

    e = &ir_table[index];
    mmio_write64(&e->irte2, DMAR_IRTE2_SVT_RID | DMAR_IRTE2_SQ_RID | DMAR_IRTE2_SID_RID(devid));
    /* set P bit last */
    mmio_write64(&e->irte1, DMAR_IRTE1_P | DMAR_IRTE1_TM_EDGE | DMAR_IRTE1_DLM_FM | DMAR_IRTE1_DM_PHYSICAL |
               DMAR_IRTE1_V(vector) | DMAR_IRTE1_DST_x2APIC(xapic_id()));
    intel_iommu_flush();
}

static void intel_iommu_reset_intremap(uint16_t index)
{
    struct dmar_irte *e;

    e = &ir_table[index];
    /* clear P bit first */
    mmio_write64(&e->irte1, 0);
    mmio_write64(&e->irte2, 0);
    intel_iommu_flush();
}

static void intel_iommu_flush(void)
{
    size_t i;

    for (i = 0; i < nr_iommus; ++i) {
        void *base = iommu_base[i];

        mmio_write64(base + DMAR_CCMD_REG, DMAR_CCMD_ICC | DMAR_CCMD_CIRG_GLOBAL);
        while (mmio_read64(base + DMAR_CCMD_REG) & DMAR_CCMD_ICC)
            pause();
        /* FIXME: flush interrupt remapping entries */
    }
}

static void intel_iommu_early_set_dev_region(physaddr_t start, physaddr_t end)
{
    size_t i;
    physaddr_t plmbase, plmlimit, phmbase, phmlimit;
    uint64_t val;

    assert(start % PAGE_SIZE == 0, "must be page-aligned");
    assert(end % PAGE_SIZE == 0, "must be page-aligned");

    plmbase = kva2pa(_start);
    plmlimit = start - 1;
    phmbase = end;
    /* FIXME: should be the end of bootmem */
    phmlimit = kva2pa(_end) - 1;
    pr_info("iommu: 0x%016" PRIx64 "-0x%016" PRIx64 ": protected low memory\n", plmbase, plmlimit);
    pr_info("iommu: 0x%016" PRIx64 "-0x%016" PRIx64 ": protected high memory\n", phmbase, phmlimit);

    for (i = 0; i < nr_iommus; ++i) {
        void *base = iommu_base[i];
        uint64_t cap;

        cap = mmio_read64(base + DMAR_CAP_REG);
        if (!((cap & DMAR_CAP_PLMR) && (cap & DMAR_CAP_PHMR))) {
            pr_warn("iommu: no plmr/phmr\n");
            continue;
        }

        /*
         * 10.4.17 Protected Low-Memory Base Register:
         *
         * The alignment of the protected low memory region base depends
         * on the number of reserved bits (N:0) of this register. Software
         * may determine N by writing all 1s to this register, and finding
         * the most significant bit position with 0 in the value read back
         * from the register. Bits N:0 of this register are decoded by
         * hardware as all 0s.
         */
        mmio_write32(base + DMAR_PLMBASE_REG, plmbase);
        val = mmio_read32(base + DMAR_PLMBASE_REG);
        if (val != plmbase) {
            pr_warn("iommu: plmbase write error: %lx %lx\n", plmbase, val);
            continue;
        }

        /*
         * 10.4.18 Protected Low-Memory Limit Register:
         *
         * The alignment of the protected low memory region limit depends
         * on the number of reserved bits (N:0) of this register. Software
         * may determine N by writing all 1’s to this register, and finding
         * most significant zero bit position with 0 in the value read back
         * from the register. Bits N:0 of the limit register are decoded by
         * hardware as all 1s.
         */
        mmio_write32(base + DMAR_PLMLIMIT_REG, plmlimit);
        val = mmio_read32(base + DMAR_PLMLIMIT_REG);
        if ((val | (SZ_2M - 1)) != plmlimit) {
            pr_warn("iommu: plmlimit write error: %lx %lx\n", plmlimit, val);
            continue;
        }

        mmio_write64(base + DMAR_PHMBASE_REG, phmbase);
        val = mmio_read64(base + DMAR_PHMBASE_REG);
        if (val != phmbase) {
            pr_warn("iommu: phmbase write error: %lx %lx\n", phmbase, val);
            continue;
        }

        mmio_write64(base + DMAR_PHMLIMIT_REG, phmlimit);
        val = mmio_read64(base + DMAR_PHMLIMIT_REG);
        if ((val | (SZ_2M - 1)) != phmlimit) {
            pr_warn("iommu: phmlimit write error: %lx %lx\n", phmlimit, val);
            continue;
        }

        /* enable PMR */
        mmio_write32(base + DMAR_PMEN_REG, DMAR_PMEN_EPM);
        while (!(mmio_read32(base + DMAR_PMEN_REG) & DMAR_PMEN_PRS))
            pause();
        pr_info("iommu: protected memory region enabled\n");
    }
}
