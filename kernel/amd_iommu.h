#pragma once

#include <uapi/cdefs.h>

#define IVRS_DEV_TABLE_BASE_OFFSET 0x00
#define IVRS_CMD_BUF_OFFSET 0x08
#define IVRS_CONTROL_OFFSET 0x18

/* IOMMU Control Register */
#define IVRS_CONTROL_IOMMU_EN BIT64(0)                /* IOMMU enable */
#define IVRS_CONTROL_DEV_TBL_SEG_EN BITMASK64(36, 34) /* Device Table Segmentation enable */

struct dev_table_entry {
    uint64_t dev0;
    uint64_t dev1;
    uint64_t dev2;
    uint64_t dev3;
} __packed;

/* [63:0] */
#define IVRS_DEV0_V BIT64(0)
#define IVRS_DEV0_TV BIT64(1)

/* [191:128] */
#define IVRS_DEV2_IV BIT64(0)
#define IVRS_DEV2_INTCTL_SHIFT (188 - 128)
#define IVRS_DEV2_INTCTL_ABORT UINT64_C(0)
#define IVRS_DEV2_INTCTL_FORWARD (UINT64_C(1) << IVRS_DEV2_INTCTL_SHIFT)
#define IVRS_DEV2_INTCTL_REMAP (UINT64_C(2) << IVRS_DEV2_INTCTL_SHIFT)
#define IVRS_DEV2_INTTABLEN_SHIFT 1

typedef uint64_t ivrs_pte_t;

#define IVRS_PTE_IW BIT64(62) /* Write permission */
#define IVRS_PTE_IR BIT64(61) /* Read permission */
#define IVRS_PTE_PERM_SHIFT 61
#define IVRS_PTE_ADDR_MASK BITS64(51, 12) /* Address mask */
#define IVRS_PTE_ADDR_SHIFT 12
#define IVRS_PTE_MODE_MASK BITS64(11, 9)
#define IVRS_PTE_MODE_SHIFT 9
#define IVRS_PTE_P BIT64(0) /* Present */

struct cmd_entry {
    uint64_t op1 : 60;
    uint64_t opcode : 3;
    uint64_t op2;
} __packed;

static_assert(sizeof(struct cmd_entry) == 16, "sizeof cmd_entry");
