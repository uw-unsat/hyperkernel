#include <uapi/machine/cpufunc.h>
#include <uapi/machine/mmu.h>
#include <uapi/machine/trap.h>
#include <cpuid.h>

void fpu_init(void)
{
#if ENABLED(CONFIG_FPU)
    register_t cr0, cr4;

    /* check xsave */
    if (!cpuid_has(CPUID_FEATURE_XSAVE))
        panic("no xsave support");

    cr0 = rcr0();
    cr0 &= ~CR0_EM;
    cr0 |= CR0_MP;

    cr4 = rcr4();
    cr4 |= CR4_OSFXSR | CR4_OSXMMEXCPT | CR4_OSXSAVE;

    lcr0(cr0);
    lcr4(cr4);

    /* TODO: avx */
    xsetbv(XCR0, XFEATURE_ENABLED_X87 | XFEATURE_ENABLED_SSE);
#endif
}

void fpu_user_init(void *data)
{
#if ENABLED(CONFIG_FPU)
    struct xsave_area *xsave_area = data;

    /* default values */
    xsave_area->fxsave_area.fcw = 0x37f;
    xsave_area->fxsave_area.ftw = 0xffff;
    xsave_area->fxsave_area.mxcsr = 0x1f80;
#endif
}
