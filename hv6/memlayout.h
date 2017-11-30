#pragma once

#include <uapi/machine/mmu.h>
#include "param.h"

#define ULIB_START UINT64_C(0xffff800000000000)

#define USYSCALL_START (ULIB_START + PAGE_SIZE)
#define USYSCALL_END (USYSCALL_START + PAGE_SIZE)

#define UPAGES_START (USYSCALL_END + PAGE_SIZE)
#define UPAGES_END (UPAGES_START + roundup(NPAGE * sizeof(struct page_desc), PAGE_SIZE))

#define UPROCS_START (UPAGES_END + PAGE_SIZE)
#define UPROCS_END (UPROCS_START + roundup(NPROC * sizeof(struct proc), PAGE_SIZE))

#define UDEVS_START (UPROCS_END + PAGE_SIZE)
#define UDEVS_END (UDEVS_START + roundup(NPCIDEV * sizeof(struct pci_dev), PAGE_SIZE))

#define UFILES_START (UDEVS_END + PAGE_SIZE)
#define UFILES_END (UFILES_START + roundup(NFILE * sizeof(struct file), PAGE_SIZE))

#define UECAM_START (UFILES_END + PAGE_SIZE)
#define UECAM_END (UECAM_START + SZ_256M)

/* 0xffff880000000000 - */
#define UVPML4_INDEX UINT64_C(272)
#define UVPT (ULIB_START | (UVPML4_INDEX << PML4_SHIFT))
#define UVPD (UVPT | (UVPML4_INDEX << PDPT_SHIFT))
#define UVPDPT (UVPD | (UVPML4_INDEX << PD_SHIFT))
#define UVPML4 (UVPDPT | (UVPML4_INDEX << PT_SHIFT))

/* leave one page unmapped at the top of the canonical lower half */
#define USTACK_TOP (BIT64(47) - PAGE_SIZE)
#define USTACK_SIZE SZ_64K

/* kernel command line */
#define UCMDLINE (USTACK_TOP - USTACK_SIZE - 2 * PAGE_SIZE)

#define UBRK_START SZ_1G
#define UPCI_START SZ_1T
