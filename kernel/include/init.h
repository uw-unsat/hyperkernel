#pragma once

void tsc_init(void);
void trap_init(void);
void cpuid_init(void);
void acpi_init(void);
void mtrr_init(void);
void pmap_init(void);
void xapic_init(void);
void pic_init(void);
void ioapic_init(void);
void fpu_init(void);
void fpu_user_init(void *);
void iommu_init(void);
