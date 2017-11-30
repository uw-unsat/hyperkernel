#pragma once

#include <uapi/cdefs.h>

/* APIC registers */
enum {
    LAPIC_ID = 0x2,
    LAPIC_VERSION = 0x3,
    LAPIC_TPR = 0x8,
    LAPIC_APR = 0x9,
    LAPIC_PPR = 0xa,
    LAPIC_EOI = 0xb,
    LAPIC_LDR = 0xd,
    LAPIC_DFR = 0xe, /* Not in x2APIC */
    LAPIC_SVR = 0xf,
    LAPIC_ISR0 = 0x10,
    LAPIC_ISR1 = 0x11,
    LAPIC_ISR2 = 0x12,
    LAPIC_ISR3 = 0x13,
    LAPIC_ISR4 = 0x14,
    LAPIC_ISR5 = 0x15,
    LAPIC_ISR6 = 0x16,
    LAPIC_ISR7 = 0x17,
    LAPIC_TMR0 = 0x18,
    LAPIC_TMR1 = 0x19,
    LAPIC_TMR2 = 0x1a,
    LAPIC_TMR3 = 0x1b,
    LAPIC_TMR4 = 0x1c,
    LAPIC_TMR5 = 0x1d,
    LAPIC_TMR6 = 0x1e,
    LAPIC_TMR7 = 0x1f,
    LAPIC_IRR0 = 0x20,
    LAPIC_IRR1 = 0x21,
    LAPIC_IRR2 = 0x22,
    LAPIC_IRR3 = 0x23,
    LAPIC_IRR4 = 0x24,
    LAPIC_IRR5 = 0x25,
    LAPIC_IRR6 = 0x26,
    LAPIC_IRR7 = 0x27,
    LAPIC_ESR = 0x28,
    LAPIC_LVT_CMCI = 0x2f,
    LAPIC_ICR_LO = 0x30,
    LAPIC_ICR_HI = 0x31, /* Not in x2APIC */
    LAPIC_LVT_TIMER = 0x32,
    LAPIC_LVT_THERMAL = 0x33,
    LAPIC_LVT_PCINT = 0x34,
    LAPIC_LVT_LINT0 = 0x35,
    LAPIC_LVT_LINT1 = 0x36,
    LAPIC_LVT_ERROR = 0x37,
    LAPIC_ICR_TIMER = 0x38,
    LAPIC_CCR_TIMER = 0x39,
    LAPIC_DCR_TIMER = 0x3e,
    LAPIC_SELF_IPI = 0x3f,     /* Only in x2APIC */
    LAPIC_EXT_FEATURES = 0x40, /* AMD */
    LAPIC_EXT_CTRL = 0x41,     /* AMD */
    LAPIC_EXT_SEOI = 0x42,     /* AMD */
    LAPIC_EXT_IER0 = 0x48,     /* AMD */
    LAPIC_EXT_IER1 = 0x49,     /* AMD */
    LAPIC_EXT_IER2 = 0x4a,     /* AMD */
    LAPIC_EXT_IER3 = 0x4b,     /* AMD */
    LAPIC_EXT_IER4 = 0x4c,     /* AMD */
    LAPIC_EXT_IER5 = 0x4d,     /* AMD */
    LAPIC_EXT_IER6 = 0x4e,     /* AMD */
    LAPIC_EXT_IER7 = 0x4f,     /* AMD */
    LAPIC_EXT_LVT0 = 0x50,     /* AMD */
    LAPIC_EXT_LVT1 = 0x51,     /* AMD */
    LAPIC_EXT_LVT2 = 0x52,     /* AMD */
    LAPIC_EXT_LVT3 = 0x53,     /* AMD */
};

/* fields in VER */
#define APIC_VER_VERSION 0x000000ff
#define APIC_VER_MAXLVT 0x00ff0000
#define MAXLVTSHIFT 16
#define APIC_VER_EOI_SUPPRESSION 0x01000000
#define APIC_VER_AMD_EXT_SPACE 0x80000000

/* fields in SVR */
#define APIC_SVR_ENABLE 0x00000100

/* fields in ICR */
#define APIC_DELMODE_FIXED 0x00000000
#define APIC_DELMODE_LOWPRIO 0x00000100
#define APIC_DELMODE_SMI 0x00000200
#define APIC_DELMODE_RR 0x00000300
#define APIC_DELMODE_NMI 0x00000400
#define APIC_DELMODE_INIT 0x00000500
#define APIC_DELMODE_STARTUP 0x00000600

#define APIC_DELSTAT_IDLE 0x00000000
#define APIC_DELSTAT_PEND 0x00001000

#define APIC_LEVEL_DEASSERT 0x00000000
#define APIC_LEVEL_ASSERT 0x00004000

#define APIC_TRIGMOD_EDGE 0x00000000
#define APIC_TRIGMOD_LEVEL 0x00008000

#define APIC_DEST_DESTFLD 0x00000000
#define APIC_DEST_SELF 0x00040000
#define APIC_DEST_ALLISELF 0x00080000
#define APIC_DEST_ALLESELF 0x000c0000

/* fields in LVT_TIMER */
#define APIC_LVTT_TM_ONE_SHOT 0x00000000
#define APIC_LVTT_TM_PERIODIC 0x00020000
#define APIC_LVTT_TM_TSCDLT 0x00040000
#define APIC_LVTT_TM_RSRV 0x00060000

/* Constants related to AMD Extended APIC Features Register */
#define APIC_EXTF_ELVT_MASK     0x00ff0000
#define APIC_EXTF_ELVT_SHIFT    16
#define APIC_EXTF_EXTID_CAP     0x00000004
#define APIC_EXTF_SEOI_CAP      0x00000002
#define APIC_EXTF_IER_CAP       0x00000001

#define APIC_LVT_M 0x00010000

#define LAPIC_MEM_MUL 0x10

void xapic_init(void);
uint32_t xapic_id(void);
void xapic_eoi(void);

void xapic_seoi(uint8_t vec);
void xapic_ier_enable(uint8_t vec);
void xapic_ier_disable(uint8_t vec);

void ioapic_enable(int irq, uint32_t apicid);
