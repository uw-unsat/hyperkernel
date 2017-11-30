#pragma once

#include <uapi/cdefs.h>

/* Version register */
#define DMAR_VER_REG 0x0
#define DMAR_MAJOR_VER(x) (((x) >> 4) & 0xf)
#define DMAR_MINOR_VER(x) ((x)&0xf)

/* Capabilities register */
#define DMAR_CAP_REG 0x8
#define DMAR_CAP_PI BIT64(59) /* Posted Interrupts */
#define DMAR_CAP_SAGAW_4LVL BIT64(10)
#define DMAR_CAP_SAGAW_3LVL BIT64(9)
#define DMAR_CAP_PHMR BIT64(6) /* Protected High-mem Region */
#define DMAR_CAP_PLMR BIT64(5) /* Protected Low-mem Region */

/* Extended Capabilities register */
#define DMAR_ECAP_REG 0x10
#define DMAR_ECAP_PASID BIT64(40)    /* Process Address Space ID Support */
#define DMAR_ECAP_PSS BITS64(39, 35) /* PASID Size Supported */
#define DMAR_ECAP_ECS BIT64(24)      /* Extended Context */
#define DMAR_ECAP_PT BIT64(6)        /* Pass Through */
#define DMAR_ECAP_EIM BIT64(4)       /* Extended Interrupt Mode (x2APIC) */
#define DMAR_ECAP_IR BIT64(3)        /* Interrupt Remapping */
#define DMAR_ECAP_DI BIT64(2)        /* Device IOTLB */

/* Global Command register */
#define DMAR_GCMD_REG 0x18
#define DMAR_GCMD_TE BIT32(31)    /* Translation Enable */
#define DMAR_GCMD_SRTP BIT32(30)  /* Set Root Table Pointer */
#define DMAR_GCMD_IRE BIT32(25)   /* Interrupt Remapping Enable */
#define DMAR_GCMD_SIRTP BIT32(24) /* Set Interrupt Remap Table Pointer */

/* Global Status register */
#define DMAR_GSTS_REG 0x1c
#define DMAR_GSTS_TES BIT32(31)  /* Translation Enable Status */
#define DMAR_GSTS_RTPS BIT32(30) /* Root Table Pointer Status */

/* Root-Entry Table Address register */
#define DMAR_RTADDR_REG 0x20
#define DMAR_RTADDR_RTT BIT64(11) /* Root Table Type */

/* Context Command register */
#define DMAR_CCMD_REG 0x28
#define DMAR_CCMD_ICC BIT64(63)            /* Invalidate Context-Cache */
#define DMAR_CCMD_CIRG_MASK BITS64(62, 61) /* Context Invalidation Request Granularity */
#define DMAR_CCMD_CIRG_GLOBAL (1ULL << 61) /*   - Global */
#define DMAR_CCMD_CIRG_DOMAIN (2ULL << 61) /*   - Domain */
#define DMAR_CCMD_CIRG_DEVICE (3ULL << 61) /*   - Device */

/* Protected Memory Enable register */
#define DMAR_PMEN_REG 0x64
#define DMAR_PMEN_EPM BIT32(31) /* Enable Protected Memory */
#define DMAR_PMEN_PRS BIT32(0) /* Protected Region Status */

/* Protected Low-Memory Base register */
#define DMAR_PLMBASE_REG 0x68

/* Protected Low-Memory Limit register */
#define DMAR_PLMLIMIT_REG 0x6c

/* Protected High-Memory Base register */
#define DMAR_PHMBASE_REG 0x70

/* Protected High-Memory Limit register */
#define DMAR_PHMLIMIT_REG 0x78

/* Interrupt Remapping Table Address register */
#define DMAR_IRTA_REG 0xb8
#define DMAR_IRTA_EIME BIT64(11)       /* Extended Interrupt Mode Enable */
#define DMAR_IRTA_S_MASK UINT64_C(0xf) /* Size Mask */

/* Root-Table Entry (sec. 9.1) */
struct dmar_root_entry {
    uint64_t r1;
    uint64_t r2; /* reserved */
} __packed;

#define DMAR_ROOT_R1_P BIT64(0)              /* Present */
#define DMAR_ROOT_R1_CTP_MASK BITS64(63, 12) /* Context Table Pointer Mask */

/* Context-Table Entry (sec 9.3) */
struct dmar_context_entry {
    uint64_t ctx1;
    uint64_t ctx2;
} __packed;

#define DMAR_CTX1_P BIT64(0)              /* Present */
#define DMAR_CTX1_FPD BIT64(1)            /* Fault Processing Disable */
#define DMAR_CTX1_T_SHIFT 2               /* Translation Type */
#define DMAR_CTX1_T_UNTR 0                /* only Untranslated */
#define DMAR_CTX1_T_TR 4                  /* both Untranslated and Translated */
#define DMAR_CTX1_T_PASS 8                /* Pass-Through */
#define DMAR_CTX1_ASR_MASK BITS64(63, 12) /* Mask for the Address Space Root */

#define DMAR_CTX2_AW_3LVL 1              /* 3-level page tables */
#define DMAR_CTX2_AW_4LVL 2              /* 4-level page tables */
#define DMAR_CTX2_DID_MASK BITS64(23, 8) /* Domain ID Mask */

typedef uint64_t dmar_pte_t;

#define DMAR_PTE_R BIT64(0)               /* Read */
#define DMAR_PTE_W BIT64(1)               /* Write */
#define DMAR_PTE_SNP BIT64(11)            /* Snoop Behaviour */
#define DMAR_PTE_ADDR_MASK BITS64(51, 12) /* Address Mask */
#define DMAR_PTE_ADDR_SHIFT 12
#define DMAR_PTE_TM BIT64(62) /* Transient Mapping */

struct dmar_irte {
    uint64_t irte1;
    uint64_t irte2;
} __packed;

/* Source Validation Type */
#define DMAR_IRTE2_SVT_NONE (UINT64_C(0) << (82 - 64))
#define DMAR_IRTE2_SVT_RID (UINT64_C(1) << (82 - 64))
#define DMAR_IRTE2_SVT_BUS (UINT64_C(2) << (82 - 64))
/* Source-id Qualifier */
#define DMAR_IRTE2_SQ_RID (UINT64_C(0) << (80 - 64))
#define DMAR_IRTE2_SQ_RID_N2 (UINT64_C(1) << (80 - 64))
#define DMAR_IRTE2_SQ_RID_N21 (UINT64_C(2) << (80 - 64))
#define DMAR_IRTE2_SQ_RID_N210 (UINT64_C(3) << (80 - 64))
/* Source Identifier */
#define DMAR_IRTE2_SID_RID(x) ((uint64_t)(x))
#define DMAR_IRTE2_SID_BUS(start, end) ((((uint64_t)(start)) << 8) | (end))
/* Destination Id */
#define DMAR_IRTE1_DST_xAPIC(x) (((uint64_t)(x)) << 40)
#define DMAR_IRTE1_DST_x2APIC(x) (((uint64_t)(x)) << 32)
/* Vector */
#define DMAR_IRTE1_V(x) (((uint64_t)x) << 16)
#define DMAR_IRTE1_IM_POSTED (UINT64_C(1) << 15) /* Posted */
/* Delivery Mode */
#define DMAR_IRTE1_DLM_FM (UINT64_C(0) << 5)
#define DMAR_IRTE1_DLM_LP (UINT64_C(1) << 5)
#define DMAR_IRTE1_DLM_SMI (UINT64_C(2) << 5)
#define DMAR_IRTE1_DLM_NMI (UINT64_C(4) << 5)
#define DMAR_IRTE1_DLM_INIT (UINT64_C(5) << 5)
#define DMAR_IRTE1_DLM_ExtINT (UINT64_C(7) << 5)
/* Trigger Mode */
#define DMAR_IRTE1_TM_EDGE (UINT64_C(0) << 4)
#define DMAR_IRTE1_TM_LEVEL (UINT64_C(1) << 4)
/* Redirection Hint */
#define DMAR_IRTE1_RH_DIRECT (UINT64_C(0) << 3)
#define DMAR_IRTE1_RH_SELECT (UINT64_C(1) << 3)
/* Destination Mode */
#define DMAR_IRTE1_DM_PHYSICAL (UINT64_C(0) << 2)
#define DMAR_IRTE1_DM_LOGICAL (UINT64_C(1) << 2)
#define DMAR_IRTE1_FPD (UINT64_C(1) << 1) /* Fault Processing Disable */
#define DMAR_IRTE1_P BIT64(0)             /* Present */

/* Posted Interrupts */
#define DMAR_IRTE2_PDAH(x) (((uint64_t)x) & BITS64(63, 32))
#define DMAR_IRTE1_PDAL(x) ((((uint64_t)x) & BITS64(31, 6)) << 32)
