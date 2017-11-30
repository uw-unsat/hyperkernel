#include <uapi/machine/cpufunc.h>
#include <uapi/machine/io.h>
#include <uapi/machine/trap.h>
#include <cpuid.h>
#include <time.h>
#include "xapic.h"

static int x2apic_mode;
static void *xapic_base;
static int seoi;

static uint32_t xapic_read32(uint32_t reg)
{
    if (x2apic_mode)
        return rdmsr(MSR_APIC_000 + reg);
    return mmio_read32(xapic_base + reg * LAPIC_MEM_MUL);
}

static void xapic_write32(uint32_t reg, uint32_t val)
{
    if (x2apic_mode)
        wrmsr(MSR_APIC_000 + reg, val);
    return mmio_write32(xapic_base + reg * LAPIC_MEM_MUL, val);
}

static void xapic_write_icr(uint64_t val)
{
    uint32_t lo, hi;

    if (x2apic_mode)
        return wrmsr(MSR_APIC_000 + LAPIC_ICR_LO, val);
    hi = val >> 32;
    lo = (uint32_t)val;
    /* write high bits first; writing lower bits will send the IPI */
    xapic_write32(LAPIC_ICR_HI, hi);
    xapic_write32(LAPIC_ICR_LO, lo);
}

static void xapic_wait(void)
{
    while (xapic_read32(LAPIC_ICR_LO) & APIC_DELSTAT_PEND)
        ;
}

void xapic_init(void)
{
    uint64_t reg;
    bool bsp;
    uint32_t ver;

    reg = rdmsr(MSR_IA32_APIC_BASE);
    assert(reg & APIC_BASE_EN, "local APIC must be enabled");
    bsp = (reg & APIC_BASE_BSP) != 0;
    x2apic_mode = cpuid_has(CPUID_FEATURE_X2APIC);
    if (x2apic_mode) {
        if (!(reg & APIC_BASE_EXTD))
            wrmsr(MSR_IA32_APIC_BASE, reg | APIC_BASE_EXTD);
    } else {
        assert(!(reg & APIC_BASE_EXTD), "no x2APIC support");
    }
    if (bsp) {
        if (x2apic_mode) {
            pr_info("xapic: x2APIC\n");
        } else {
            xapic_base = (void *)(reg & APIC_BASE_ADDRESS_MASK);
            pr_info("xapic: xAPIC starting at 0x%016" PRIxPTR "\n", (uintptr_t)xapic_base);
        }
    }

    ver = xapic_read32(LAPIC_VERSION);
    pr_info("xapic: version %x\n", ver);
    if (ver & APIC_VER_AMD_EXT_SPACE) {
        uint32_t extf = xapic_read32(LAPIC_EXT_FEATURES), ctrl;

        if ((extf & APIC_EXTF_SEOI_CAP) && (extf & APIC_EXTF_IER_CAP)) {
            ctrl = xapic_read32(LAPIC_EXT_CTRL);
            ctrl |= (APIC_EXTF_SEOI_CAP | APIC_EXTF_IER_CAP);
            xapic_write32(LAPIC_EXT_CTRL, ctrl);
            seoi = 1;
            pr_info("xapic: enable SEOI\n");
        }
    }

    /* enable local APIC; set spurious interrupt vector */
    xapic_write32(LAPIC_SVR, APIC_SVR_ENABLE | (TRAP_IRQ0 + IRQ_SPURIOUS));

#if 0
	/* the timer repeatedly counts down at bus frequency from ICR_TIMER and then issues an interrupt */
	xapic_write32(LAPIC_DCR_TIMER, 0x0000000b);
	xapic_write32(LAPIC_LVT_TIMER, APIC_LVTT_TM_PERIODIC | (TRAP_IRQ0 + IRQ_TIMER));
	xapic_write32(LAPIC_ICR_TIMER, 10000000);
#endif

    /* disable logical interrupt lines */
    xapic_write32(LAPIC_LVT_LINT0, APIC_LVT_M);
    xapic_write32(LAPIC_LVT_LINT1, APIC_LVT_M);

    /* disable performance counter overflow interrupts */
    xapic_write32(LAPIC_LVT_PCINT, APIC_LVT_M);

    /* map error interrupt to IRQ_ERROR */
    xapic_write32(LAPIC_LVT_ERROR, TRAP_IRQ0 + IRQ_ERROR);

    /* clear error status register (requires back-to-back writes) */
    xapic_write32(LAPIC_ESR, 0);
    xapic_write32(LAPIC_ESR, 0);

    /* ack any outstanding interrupts */
    xapic_write32(LAPIC_EOI, 0);

    /* send an Init Level De-Assert to synchronise arbitration ID's */
    xapic_write_icr(APIC_DEST_ALLISELF | APIC_DELMODE_INIT | APIC_TRIGMOD_LEVEL |
                    APIC_LEVEL_DEASSERT);
    xapic_wait();

    /* enable interrupts on the APIC (but not on the processor) */
    xapic_write32(LAPIC_TPR, 0);
}

uint32_t xapic_id(void)
{
    uint32_t id = xapic_read32(LAPIC_ID);

    return x2apic_mode ? id : (id >> 24);
}

void xapic_eoi(void)
{
    xapic_write32(LAPIC_EOI, 0);
}

void xapic_seoi(uint8_t vec)
{
    if (!seoi)
        return;

    xapic_write32(LAPIC_EXT_SEOI, vec);
}

void xapic_ier_enable(uint8_t vec)
{
    uint32_t reg, val;

    if (!seoi)
        return;

    reg = LAPIC_EXT_IER0 + vec / 32;
    val = xapic_read32(reg) | BIT32(vec % 32);
    xapic_write32(reg, val);
}

void xapic_ier_disable(uint8_t vec)
{
    uint32_t reg, val;

    if (!seoi)
        return;

    reg = LAPIC_EXT_IER0 + vec / 32;
    val = xapic_read32(reg) & ~BIT32(vec % 32);
    xapic_write32(reg, val);
}
