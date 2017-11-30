#pragma once

#include "param.h"
#include "types.h"

extern struct pci_dev devices[NPCIDEV];
extern volatile uint8_t dmapages[NDMAPAGE][PAGE_SIZE];

int sys_map_pcipage(pn_t pt, size_t index, pn_t pcipn, pte_t perm);
/*
 * We don't have sys_unmap_pcipage here as it's not useful.
 * We assume the common use of a process (e.g., servers) is
 * not to give up pci pages until it's dead.
 */

int sys_alloc_iommu_root(devid_t devid, pn_t pn);
int sys_alloc_iommu_pdpt(pn_t from, size_t index, pn_t to, iommu_pte_t perm);
int sys_alloc_iommu_pd(pn_t from, size_t index, pn_t to, iommu_pte_t perm);
int sys_alloc_iommu_pt(pn_t from, size_t index, pn_t to, iommu_pte_t perm);
int sys_alloc_iommu_frame(pn_t from, size_t index, dmapn_t to, iommu_pte_t perm);
int sys_map_iommu_frame(pn_t pt, size_t index, dmapn_t to, pte_t perm);
int sys_reclaim_iommu_frame(dmapn_t dmapn);
/*
 * iommu root is only reclaimed for zombies; this is easier to reclaim
 * other resources (e.g., pcipages).
 */
int sys_reclaim_iommu_root(devid_t devid);

int sys_alloc_vector(uint8_t vector);
/*
 * There is no free here; IR table might refer to a vector.
 */
int sys_reclaim_vector(uint8_t vector);
void reserve_vector(uint8_t vector);
void reserve_vectors(uint8_t vector, size_t n);

int sys_alloc_intremap(size_t index, devid_t devid, uint8_t irq);
int sys_reclaim_intremap(size_t index);
int sys_ack_intr(uint8_t irq);

int extintr(uint8_t irq);

void device_add(struct pci_func *f);
