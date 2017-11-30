#pragma once

#include <uapi/cdefs.h>

#define SEG_A BIT64(40)
#define SEG_W BIT64(41)
#define SEG_CODE BIT64(43)
#define SEG_S BIT64(44)
#define SEG_DPL(dpl) (((dpl)&UINT64_C(3)) << 45)
#define SEG_P BIT64(47)
#define SEG_L BIT64(53)
#define SEG_G BIT64(55)

#define SEG_TSSA (UINT64_C(9) << 40)
#define SEG_LIMIT(x) (((x)&0xffff) | ((x)&UINT64_C(0xf0000)) << 32)
#define SEG_BASELO(x) ((((x)&0xffffff) << 16) | (((x)&0xff000000) << 32))
#define SEG_BASEHI(x) ((x) >> 32)

/* system segment type bits */
#define STS_LDT 0x2  /* local descriptor table */
#define STS_T64A 0x9 /* available 64-bit TSS */
#define STS_T64B 0xb /* busy 64-bit TSS */
#define STS_CG64 0xc /* 64-bit call gate */
#define STS_IG64 0xe /* 64-bit interrupt gate */
#define STS_TG64 0xf /* 64-bit trap gate */

/* privilege levels */
#define KERNEL_PL 0
#define USER_PL 3

#define KERNEL_DS_DESC (SEG_P | SEG_S | SEG_DPL(KERNEL_PL) | SEG_A | SEG_W | SEG_G)
#define KERNEL_CS_DESC (SEG_CODE | SEG_L | KERNEL_DS_DESC)

#ifndef __ASSEMBLER__

struct tss {
    uint32_t reserved0;
    uint64_t rsp0;
    uint64_t rsp1;
    uint64_t rsp2;
    uint64_t reserved1;
    uint64_t ist1;
    uint64_t ist2;
    uint64_t ist3;
    uint64_t ist4;
    uint64_t ist5;
    uint64_t ist6;
    uint64_t ist7;
    uint64_t reserved2;
    uint16_t reserved3;
    uint16_t iomb;
} __packed;

/* gate descriptors for interrupts and traps */
struct gate_desc {
    unsigned long off_15_0 : 16;  // low 16 bits of offset in segment
    unsigned long sel : 16;       // segment selector
    unsigned long ist : 3;        // interrupt stack table
    unsigned long rsv1 : 5;       // reserved(should be zero I guess)
    unsigned long type : 4;       // type(STS_{TG,IG64,TG64})
    unsigned long s : 1;          // must be 0 (system)
    unsigned long dpl : 2;        // descriptor(meaning new) privilege level
    unsigned long p : 1;          // Present
    unsigned long off_31_16 : 16; // high bits of offset in segment
    unsigned long off_63_32 : 32; // really high bits of offset
    unsigned long rsv2 : 32;      // reserved
} __packed;

/* gdt/idt descriptor */
struct pseudo_desc {
    uint16_t limit;
    uint64_t base;
} __packed;

static_assert(sizeof(struct gate_desc) == 16, "gate_desc size 16");

static inline void set_gate_desc(struct gate_desc *gd, bool istrap, uint16_t sel, void *ptr,
                                 int dpl)
{
    uintptr_t off = (uintptr_t)ptr;

    gd->off_15_0 = (off >> 0) & 0xffff;
    gd->sel = sel;
    gd->ist = 0;
    gd->rsv1 = 0;
    gd->type = istrap ? STS_TG64 : STS_IG64;
    gd->s = 0;
    gd->dpl = dpl;
    gd->p = 1;
    gd->off_31_16 = (off >> 16) & 0xffff;
    gd->off_63_32 = (off >> 32) & 0xffffffff;
    gd->rsv2 = 0;
}

#endif /* !__ASSEMBLER__ */
