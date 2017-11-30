#pragma once

#include <uapi/cdefs.h>

#define CR0_PE BIT32(0)  /* protected-mode enable */
#define CR0_MP BIT32(1)  /* monitor coprocessor */
#define CR0_EM BIT32(2)  /* emulate coprocessor */
#define CR0_TS BIT32(3)  /* task switched */
#define CR0_ET BIT32(4)  /* reserved to be 1 */
#define CR0_NE BIT32(5)  /* numeric error */
#define CR0_WP BIT32(16) /* write protect */
#define CR0_PG BIT32(31) /* paging enable */

#define CR4_PSE BIT32(4)
#define CR4_PAE BIT32(5)
#define CR4_MCE BIT32(6)
#define CR4_PGE BIT32(7)
#define CR4_OSFXSR BIT32(9)
#define CR4_OSXMMEXCPT BIT32(10)
#define CR4_VMXE BIT32(13)
#define CR4_FSGSBASE BIT32(16)
#define CR4_OSXSAVE BIT32(18)

/* extended control register */
#define XCR0 0

#define XFEATURE_ENABLED_X87 BIT64(0)
#define XFEATURE_ENABLED_SSE BIT64(1)
#define XFEATURE_ENABLED_AVX BIT64(2)

#define FLAGS_CF BIT64(0)    /* carry flag */
#define FLAGS_FIXED BIT64(1) /* always 1 */
#define FLAGS_PF BIT64(2)    /* parity flag */
/* 3 - reserved */
#define FLAGS_AF BIT64(4) /* adjust flag */
/* 5 - reserved */
#define FLAGS_ZF BIT64(6)         /* zero flag */
#define FLAGS_SF BIT64(7)         /* sign flag */
#define FLAGS_TF BIT64(8)         /* trap flag */
#define FLAGS_IF BIT64(9)         /* interrupt flag */
#define FLAGS_DF BIT64(10)        /* direction flag */
#define FLAGS_OF BIT64(11)        /* overflow flag */
#define FLAGS_IOPL BITS64(13, 12) /* I/O privilege level */
#define FLAGS_NT BIT64(14)        /* nested task flag */
/* 15 - reserved */
#define FLAGS_RF BIT64(16)  /* resume flag */
#define FLAGS_VM BIT64(17)  /* virtual 8086 mode flag */
#define FLAGS_AC BIT64(18)  /* alignment check */
#define FLAGS_VIF BIT64(19) /* virtual interrupt flag */
#define FLAGS_VIP BIT64(20) /* virtual interrupt pending */
#define FLAGS_ID BIT64(21)  /* can use CPUID */

#define PTE_P BIT64(0)   /* present */
#define PTE_W BIT64(1)   /* writable */
#define PTE_U BIT64(2)   /* user */
#define PTE_PWT BIT64(3) /* write through */
#define PTE_PCD BIT64(4) /* cache disable */
#define PTE_A BIT64(5)   /* accessed */
#define PTE_D BIT64(6)   /* dirty */
#define PTE_PS BIT64(7)  /* page size */
#define PTE_G BIT64(8)   /* global */
#define PTE_AVL BITMASK64(11, 9)
#define PTE_NX BIT64(63) /* execute disable */

#define PTE_ADDR(pte) ((physaddr_t)(pte)&BITMASK64(51, 12))
#define PTE_PERM_MASK (PTE_P | PTE_W | PTE_U | PTE_PWT | PTE_PCD | PTE_AVL | PTE_NX)
#define PTE_PFN_SHIFT 12

#define PAGE_SHIFT 12
#define PAGE_SIZE (UINT64_C(1) << PAGE_SHIFT)

#define PML4_SHIFT 39
#define PTRS_PER_PML4 UINT64_C(512)
#define CAP_TYPE_X86_PML4 CAP_TYPE_PAGEMAP_L3

#define PDPT_SHIFT 30
#define PTRS_PER_PDPT UINT64_C(512)
#define CAP_TYPE_X86_PDPT CAP_TYPE_PAGEMAP_L2

#define PD_SHIFT 21
#define PTRS_PER_PD UINT64_C(512)
#define PD_SIZE (UINT64_C(1) << PD_SHIFT)
#define CAP_TYPE_X86_PD CAP_TYPE_PAGEMAP_L1

#define PT_SHIFT 12
#define PTRS_PER_PT UINT64_C(512)
#define CAP_TYPE_X86_PT CAP_TYPE_PAGEMAP_L0

#define PML4_INDEX(va) ((UINTPTR_T(va) >> PML4_SHIFT) & (PTRS_PER_PML4 - 1))

#define PDPT_INDEX(va) ((UINTPTR_T(va) >> PDPT_SHIFT) & (PTRS_PER_PDPT - 1))

#define PD_INDEX(va) ((UINTPTR_T(va) >> PD_SHIFT) & (PTRS_PER_PD - 1))

#define PT_INDEX(va) ((UINTPTR_T(va) >> PT_SHIFT) & (PTRS_PER_PT - 1))

#ifndef __ASSEMBLER__

static inline bool pte_valid(uintptr_t x)
{
    return x & PTE_P;
}

static inline bool pte_writable(uintptr_t x)
{
    return x & PTE_W;
}

static inline bool pte_executable(uintptr_t x)
{
    return !(x & PTE_NX);
}

static inline bool pte_dirty(uintptr_t x)
{
    return x & PTE_D;
}

static inline bool pte_user(uintptr_t x)
{
    return x & PTE_U;
}

static inline bool pte_accessed(uintptr_t x)
{
    return x & PTE_A;
}

#endif
