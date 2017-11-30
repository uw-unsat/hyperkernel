#include <uapi/pci.h>
#include <uapi/sysctl.h>
#include <iommu.h>
#include <time.h>
#include "types.h"

uint64_t sys_debug_sysctl(uint64_t id)
{
    switch (id) {
    case SYSCTL_ECAM_ADDRESS:
        return pci_config_base;
    case SYSCTL_IOMMU_VENDOR:
        return iommu_vendor;
    case SYSCTL_TSC_KHZ:
        return ms_to_cycles(1);
    }

    return UINT64_MAX;
}
