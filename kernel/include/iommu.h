#pragma once

#include <uapi/cdefs.h>

extern uint16_t iommu_vendor;
extern void (*iommu_reset_dev_root)(uint16_t id);
extern void (*iommu_set_dev_root)(uint16_t id, physaddr_t addr);
extern uint64_t (*iommu_entry)(uint64_t addr, uint64_t perm, size_t level);
extern void (*iommu_set_intremap)(uint16_t index, uint16_t id, uint8_t irq);
extern void (*iommu_reset_intremap)(uint16_t index);
extern void (*iommu_flush)(void);
extern void (*iommu_early_set_dev_region)(physaddr_t start, physaddr_t end);
