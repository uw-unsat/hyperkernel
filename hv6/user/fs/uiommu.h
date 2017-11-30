#pragma once

#include "user.h"

pn_t iommu_alloc_root(size_t i, uintptr_t va, int bar);
void iommu_map(pn_t root, void *va, size_t n);
