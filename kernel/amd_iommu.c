#include <uapi/machine/cpufunc.h>
#include <uapi/machine/mmu.h>
#include <uapi/pcidb.h>
#include <acpi.h>
#include <iommu.h>
#include <string.h>
#include "amd_iommu.h"

/* 2MB device table */
static struct dev_table_entry dev_table[SZ_64K] __aligned(PAGE_SIZE);

static void amd_iommu_reset_dev_root(uint16_t id);
static void amd_iommu_set_dev_root(uint16_t id, physaddr_t addr);
static uint64_t amd_iommu_entry(uint64_t addr, uint64_t perm, uint64_t level);
static void amd_iommu_set_intremap(uint16_t index, uint16_t id, uint8_t irq);
static void amd_iommu_reset_intremap(uint16_t index);
static void amd_iommu_flush(void);
static void amd_iommu_early_set_dev_region(physaddr_t start, physaddr_t end);

void amd_iommu_init(void)
{
    acpi_status status;
    struct acpi_table_ivrs *ivrs;
    struct acpi_ivrs_header *hdr, *end;

    status = acpi_get_table(ACPI_SIG_IVRS, 0, (struct acpi_table_header **)&ivrs);
    assert(ACPI_SUCCESS(status), "IVRS not found");
    hdr = (void *)ivrs + sizeof(*ivrs);
    end = (void *)ivrs + ivrs->header.length;

    for (; hdr < end; hdr = (void *)hdr + hdr->length) {
        struct acpi_ivrs_hardware *ivhd;
        void *base;
        uint64_t ctrl;

        if (hdr->type != ACPI_IVRS_TYPE_HARDWARE)
            continue;
        ivhd = (void *)hdr;
        base = (void *)ivhd->base_address;
        pr_info("iommu: IVHD base address 0x%016" PRIxPTR "\n", (uintptr_t)base);
        /* set device table base address */
        mmio_write64(base + IVRS_DEV_TABLE_BASE_OFFSET, (uintptr_t)dev_table | 0x1ff);
        /* enable iommu */
        ctrl = mmio_read64(base + IVRS_CONTROL_OFFSET);
        assert(bit_get_field(ctrl, IVRS_CONTROL_DEV_TBL_SEG_EN) == 0,
               "no device table segmentation");
        ctrl |= IVRS_CONTROL_IOMMU_EN;
        mmio_write64(base + IVRS_CONTROL_OFFSET, ctrl);
    }

    iommu_vendor = PCI_VENDOR_AMD;
    iommu_reset_dev_root = amd_iommu_reset_dev_root;
    iommu_set_dev_root = amd_iommu_set_dev_root;
    iommu_entry = amd_iommu_entry;
    iommu_set_intremap = amd_iommu_set_intremap;
    iommu_reset_intremap = amd_iommu_reset_intremap;
    iommu_flush = amd_iommu_flush;
    iommu_early_set_dev_region = amd_iommu_early_set_dev_region;
}

static void amd_iommu_reset_dev_root(uint16_t id)
{
    struct dev_table_entry *e = &dev_table[id];

    /* clear V bit first */
    mmio_write64(&e->dev0, 0);
    mmio_write64(&e->dev1, 0);
    mmio_write64(&e->dev2, 0);
    mmio_write64(&e->dev3, 0);
    amd_iommu_flush();
}

static void amd_iommu_set_dev_root(uint16_t id, physaddr_t addr)
{
    struct dev_table_entry *e = &dev_table[id];

    mmio_write64(&e->dev3, 0);
    mmio_write64(&e->dev2, 0);
    mmio_write64(&e->dev1, 0);
    /* set V bit last */
    mmio_write64(&e->dev0,
                 addr | IVRS_DEV0_V | IVRS_DEV0_TV |
                 (4 << IVRS_PTE_MODE_SHIFT) | IVRS_PTE_IR | IVRS_PTE_IW);
    amd_iommu_flush();
}

static uint64_t amd_iommu_entry(uint64_t addr, uint64_t perm, uint64_t level)
{
    return IVRS_PTE_P | addr | (perm << IVRS_PTE_PERM_SHIFT) | (level << IVRS_PTE_MODE_SHIFT);
}

static void amd_iommu_set_intremap(uint16_t index, uint16_t devid, uint8_t vector)
{
    /* TODO */
}

static void amd_iommu_reset_intremap(uint16_t index)
{
    /* TODO */
}

static void amd_iommu_flush(void)
{
    /* TODO */
}

static void amd_iommu_early_set_dev_region(physaddr_t start, physaddr_t end)
{
    /* TODO */
}
