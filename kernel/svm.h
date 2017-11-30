#pragma once

#include <uapi/cdefs.h>

#define VMCB_CR_INTCPT 0
#define VMCB_DR_INTCPT 1
#define VMCB_EXC_INTCPT 2
#define VMCB_CTRL1_INTCPT 3
#define VMCB_CTRL2_INTCPT 4

/* VMCB_CR_INTCPT */
#define VMCB_INTCPT_CR3_READ BIT32(3)
#define VMCB_INTCPT_CR3_WRITE BIT32(16 + 3)

/* VMCB_CTRL1_INTCPT */
#define VMCB_INTCPT_INTR                BIT32(0)
#define VMCB_INTCPT_NMI                 BIT32(1)
#define VMCB_INTCPT_SMI                 BIT32(2)
#define VMCB_INTCPT_INIT                BIT32(3)
#define VMCB_INTCPT_VINTR               BIT32(4)
#define VMCB_INTCPT_CR0_WRITE           BIT32(5)
#define VMCB_INTCPT_IDTR_READ           BIT32(6)
#define VMCB_INTCPT_GDTR_READ           BIT32(7)
#define VMCB_INTCPT_LDTR_READ           BIT32(8)
#define VMCB_INTCPT_TR_READ             BIT32(9)
#define VMCB_INTCPT_IDTR_WRITE          BIT32(10)
#define VMCB_INTCPT_GDTR_WRITE          BIT32(11)
#define VMCB_INTCPT_LDTR_WRITE          BIT32(12)
#define VMCB_INTCPT_TR_WRITE            BIT32(13)
#define VMCB_INTCPT_RDTSC               BIT32(14)
#define VMCB_INTCPT_RDPMC               BIT32(15)
#define VMCB_INTCPT_PUSHF               BIT32(16)
#define VMCB_INTCPT_POPF                BIT32(17)
#define VMCB_INTCPT_CPUID               BIT32(18)
#define VMCB_INTCPT_RSM                 BIT32(19)
#define VMCB_INTCPT_IRET                BIT32(20)
#define VMCB_INTCPT_INTn                BIT32(21)
#define VMCB_INTCPT_INVD                BIT32(22)
#define VMCB_INTCPT_PAUSE               BIT32(23)
#define VMCB_INTCPT_HLT                 BIT32(24)
#define VMCB_INTCPT_INVPG               BIT32(25)
#define VMCB_INTCPT_INVPGA              BIT32(26)
#define VMCB_INTCPT_IO                  BIT32(27)
#define VMCB_INTCPT_MSR                 BIT32(28)
#define VMCB_INTCPT_TASK_SWITCH         BIT32(29)
#define VMCB_INTCPT_FERR_FREEZE         BIT32(30)
#define VMCB_INTCPT_SHUTDOWN            BIT32(31)

/* VMCB_CTRL2_INTCPT */
#define VMCB_INTCPT_VMRUN               BIT32(0)
#define VMCB_INTCPT_VMMCALL             BIT32(1)
#define VMCB_INTCPT_VMLOAD              BIT32(2)
#define VMCB_INTCPT_VMSAVE              BIT32(3)
#define VMCB_INTCPT_STGI                BIT32(4)
#define VMCB_INTCPT_CLGI                BIT32(5)
#define VMCB_INTCPT_SKINIT              BIT32(6)
#define VMCB_INTCPT_RDTSCP              BIT32(7)
#define VMCB_INTCPT_ICEBP               BIT32(8)
#define VMCB_INTCPT_WBINVD              BIT32(9)
#define VMCB_INTCPT_MONITOR             BIT32(10)
#define VMCB_INTCPT_MWAIT               BIT32(11)
#define VMCB_INTCPT_MWAIT_ARMED         BIT32(12)
#define VMCB_INTCPT_XSETBV              BIT32(13)

/* VMCB TLB control */
#define VMCB_TLB_FLUSH_NOTHING          0       /* Flush nothing */
#define VMCB_TLB_FLUSH_ALL              1       /* Flush entire TLB */
#define VMCB_TLB_FLUSH_GUEST            3       /* Flush all guest entries */
#define VMCB_TLB_FLUSH_GUEST_NONGLOBAL  7       /* Flush guest non-PG entries */

/* VMCB state caching */
#define VMCB_CACHE_NONE         0         /* No caching */
#define VMCB_CACHE_I            BIT32(0)  /* Intercept, TSC off, Pause filter */
#define VMCB_CACHE_IOPM         BIT32(1)  /* I/O and MSR permission */
#define VMCB_CACHE_ASID         BIT32(2)  /* ASID */
#define VMCB_CACHE_TPR          BIT32(3)  /* V_TPR to V_INTR_VECTOR */
#define VMCB_CACHE_NP           BIT32(4)  /* Nested Paging */
#define VMCB_CACHE_CR           BIT32(5)  /* CR0, CR3, CR4 & EFER */
#define VMCB_CACHE_DR           BIT32(6)  /* Debug registers */
#define VMCB_CACHE_DT           BIT32(7)  /* GDT/IDT */
#define VMCB_CACHE_SEG          BIT32(8)  /* User segments, CPL */
#define VMCB_CACHE_CR2          BIT32(9)  /* page fault address */
#define VMCB_CACHE_LBR          BIT32(10) /* Last branch */

/* VMCB control event injection */
#define VMCB_EVENTINJ_EC_VALID          BIT64(11) /* Error Code valid */
#define VMCB_EVENTINJ_VALID             BIT64(31) /* Event valid */

/* Event types that can be injected */
#define VMCB_EVENTINJ_TYPE_INTR         0
#define VMCB_EVENTINJ_TYPE_NMI          2
#define VMCB_EVENTINJ_TYPE_EXCEPTION    3
#define VMCB_EVENTINJ_TYPE_INTn         4

/* VMCB exit code */
#define VMCB_EXIT_MC 0x52
#define VMCB_EXIT_INTR 0x60
#define VMCB_EXIT_NMI 0x61
#define VMCB_EXIT_VINTR 0x64
#define VMCB_EXIT_PUSHF 0x70
#define VMCB_EXIT_POPF 0x71
#define VMCB_EXIT_CPUID 0x72
#define VMCB_EXIT_IRET 0x74
#define VMCB_EXIT_PAUSE 0x77
#define VMCB_EXIT_HLT 0x78
#define VMCB_EXIT_IO 0x7b
#define VMCB_EXIT_MSR 0x7C
#define VMCB_EXIT_SHUTDOWN 0x7f
#define VMCB_EXIT_VMRUN 0x80
#define VMCB_EXIT_VMMCALL 0x81
#define VMCB_EXIT_VMLOAD 0x82
#define VMCB_EXIT_VMSAVE 0x83
#define VMCB_EXIT_MONITOR 0x8a
#define VMCB_EXIT_MWAIT 0x8b
#define VMCB_EXIT_NPF 0x400

#ifndef __ASSEMBLER__

/* VMCB save state area segment format */
struct vmcb_segment {
    uint16_t selector;
    uint16_t attrib;
    uint32_t limit;
    uint64_t base;
} __packed;

/* VMCB control area - padded up to 1024 bytes */
struct vmcb_ctrl {
    uint32_t intercept[5];
    uint8_t pad1[0x28];       /* Offsets 0x14-0x3B are reserved. */
    uint16_t pause_filthresh; /* Offset 0x3C, PAUSE filter threshold */
    uint16_t pause_filcnt;    /* Offset 0x3E, PAUSE filter count */
    uint64_t iopm_base_pa;    /* 0x40: IOPM_BASE_PA */
    uint64_t msrpm_base_pa;   /* 0x48: MSRPM_BASE_PA */
    uint64_t tsc_offset;      /* 0x50: TSC_OFFSET */
    uint32_t asid;            /* 0x58: Guest ASID */
    uint8_t tlb_ctrl;         /* 0x5C: TLB_CONTROL */
    uint8_t pad2[3];          /* 0x5D-0x5F: Reserved. */
    uint8_t v_tpr;            /* 0x60: V_TPR, guest CR8 */
    uint8_t v_irq : 1;        /* Is virtual interrupt pending? */
    uint8_t : 7;              /* Padding */
    uint8_t v_intr_prio : 4;  /* 0x62: Priority for virtual interrupt. */
    uint8_t v_ign_tpr : 1;
    uint8_t : 3;
    uint8_t v_intr_masking : 1; /* Guest and host sharing of RFLAGS. */
    uint8_t : 7;
    uint8_t v_intr_vector;    /* 0x65: Vector for virtual interrupt. */
    uint8_t pad3[3];          /* Bit64-40 Reserved. */
    uint64_t intr_shadow : 1; /* 0x68: Interrupt shadow, section15.2.1 APM2 */
    uint64_t : 63;
    uint64_t exitcode;      /* 0x70, Exitcode */
    uint64_t exitinfo1;     /* 0x78, EXITINFO1 */
    uint64_t exitinfo2;     /* 0x80, EXITINFO2 */
    uint64_t exitintinfo;   /* 0x88, Interrupt exit value. */
    uint64_t np_enable : 1; /* 0x90, Nested paging enable. */
    uint64_t : 63;
    uint8_t pad4[0x10];       /* 0x98-0xA7 reserved. */
    uint64_t eventinj;        /* 0xA8, Event injection. */
    uint64_t n_cr3;           /* B0, Nested page table. */
    uint64_t lbr_virt_en : 1; /* Enable LBR virtualization. */
    uint64_t : 63;
    uint32_t vmcb_clean; /* 0xC0: VMCB clean bits for caching */
    uint32_t : 32;       /* 0xC4: Reserved */
    uint64_t nrip;       /* 0xC8: Guest next nRIP. */
    uint8_t inst_len;    /* 0xD0: #NPF decode assist */
    uint8_t inst_bytes[15];
    uint8_t padd6[0x320];
} __packed;

_Static_assert(sizeof(struct vmcb_ctrl) == SZ_1K, "the control area is padded to 1KB");

struct vmcb_state {
    struct vmcb_segment es;
    struct vmcb_segment cs;
    struct vmcb_segment ss;
    struct vmcb_segment ds;
    struct vmcb_segment fs;
    struct vmcb_segment gs;
    struct vmcb_segment gdt;
    struct vmcb_segment ldt;
    struct vmcb_segment idt;
    struct vmcb_segment tr;
    uint8_t pad1[0x2b]; /* Reserved: 0xa0-0xca */
    uint8_t cpl;
    uint8_t pad2[4];
    uint64_t efer;
    uint8_t pad3[0x70]; /* Reserved: 0xd8-0x147 */
    uint64_t cr4;
    uint64_t cr3; /* Guest CR3 */
    uint64_t cr0;
    uint64_t dr7;
    uint64_t dr6;
    uint64_t rflags;
    uint64_t rip;
    uint8_t pad4[0x58]; /* Reserved: 0x180-0x1d7 */
    uint64_t rsp;
    uint8_t pad5[0x18]; /* Reserved: 0x1e0-0x1f7 */
    uint64_t rax;
    uint64_t star;
    uint64_t lstar;
    uint64_t cstar;
    uint64_t sfmask;
    uint64_t kernelgsbase;
    uint64_t sysenter_cs;
    uint64_t sysenter_esp;
    uint64_t sysenter_eip;
    uint64_t cr2;
    uint8_t pad6[0x20]; /* Reserved: 0x248-0x267 */
    uint64_t g_pat;
    uint64_t dbgctl;
    uint64_t br_from;
    uint64_t br_to;
    uint64_t int_from;
    uint64_t int_to;
    /* the following is for SEV-ES */
    uint8_t pad7[0x300 - 0x298]; /* XXX: AMD manual says qword */
    uint64_t pad8;               /* RAX already stored at offset 0x1f8 */
    uint64_t rcx;
    uint64_t rdx;
    uint64_t rbx;
    uint64_t pad9; /* RSP already stored at offset 0x1d8 */
    uint64_t rbp;
    uint64_t rsi;
    uint64_t rdi;
    uint64_t r8;
    uint64_t r9;
    uint64_t r10;
    uint64_t r11;
    uint64_t r12;
    uint64_t r13;
    uint64_t r14;
    uint64_t r15;
    uint8_t pad10[16]; /* Reserved: 0x380-0x38f */
    uint64_t sw_exitcode;
    uint64_t sw_exitinfo1;
    uint64_t sw_exitinfo2;
    uint64_t sw_scratch;
    uint8_t pad11[56]; /* Reserved: 0x3b0-0x3e7 */
    uint64_t xcr0;
    uint8_t valid_bitmap[16];
    uint64_t x87_dp;
    uint32_t mxcsr;
    uint16_t x87_ftw;
    uint16_t x87_fsw;
    uint16_t x87_fcw;
    uint16_t x87_fop;
    uint16_t x87_ds;
    uint16_t x87_cs;
    uint64_t x87_rip;
    uint8_t fpreg_x87[80];
    uint8_t fpreg_xmm[256];
    uint8_t fpreg_ymm[256];
} __packed;

_Static_assert(sizeof(struct vmcb_state) == 0x670, "the state save area must be 0x670 bytes");

struct vmcb {
    struct vmcb_ctrl ctrl;
    struct vmcb_state state;
} __packed;

_Static_assert(sizeof(struct vmcb) <= SZ_4K, "VMCB must fit in one page");

#endif /* !__ASSEMBLER__ */
