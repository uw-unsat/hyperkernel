#include <acpi.h>
#include <iommu.h>

uint16_t iommu_vendor;
void (*iommu_reset_dev_root)(uint16_t id);
void (*iommu_set_dev_root)(uint16_t id, physaddr_t addr);
uint64_t (*iommu_entry)(uint64_t addr, uint64_t perm, size_t level);
void (*iommu_set_intremap)(uint16_t index, uint16_t devid, uint8_t vector);
void (*iommu_reset_intremap)(uint16_t index);
void (*iommu_flush)(void);
void (*iommu_early_set_dev_region)(physaddr_t start, physaddr_t end);

void intel_iommu_init(void);
void amd_iommu_init(void);

static void stub_iommu_reset_dev_root(uint16_t id)
{
}
static void stub_iommu_set_dev_root(uint16_t id, physaddr_t addr)
{
}
extern uint64_t stub_iommu_entry(uint64_t addr, uint64_t perm, uint64_t level)
{
    return 0;
}
static void stub_iommu_set_intremap(uint16_t index, uint16_t id, uint8_t irq)
{
}
static void stub_iommu_reset_intremap(uint16_t index)
{
}
static void stub_iommu_flush(void)
{
}
static void stub_iommu_early_set_dev_region(physaddr_t start, physaddr_t end)
{
}

void iommu_init(void)
{
    acpi_status status;
    struct acpi_table_header *header;

    status = acpi_get_table(ACPI_SIG_DMAR, 0, &header);
    if (ACPI_SUCCESS(status))
        return intel_iommu_init();

    status = acpi_get_table(ACPI_SIG_IVRS, 0, &header);
    if (ACPI_SUCCESS(status))
        return amd_iommu_init();

    pr_warn("iommu: DMAR/IVRS not found\n");
    iommu_reset_dev_root = stub_iommu_reset_dev_root;
    iommu_set_dev_root = stub_iommu_set_dev_root;
    iommu_entry = stub_iommu_entry;
    iommu_set_intremap = stub_iommu_set_intremap;
    iommu_reset_intremap = stub_iommu_reset_intremap;
    iommu_flush = stub_iommu_flush;
    iommu_early_set_dev_region = stub_iommu_early_set_dev_region;
}
