#include <uapi/machine/cpufunc.h>
#include <cpuid.h>

static char *names[] = {
        [MTRR_UNCACHEABLE] = "uncacheable",     [MTRR_WRITE_COMBINING] = "write-combining",
        [MTRR_WRITE_THROUGH] = "write-through", [MTRR_WRITE_PROTECTED] = "write-protected",
        [MTRR_WRITE_BACK] = "write-back",
};

void mtrr_init(void)
{
    uint64_t cap;
    size_t vcnt, i;

    if (!cpuid_has(CPUID_FEATURE_MTRR))
        return;
    cap = rdmsr(MSR_IA32_MTRRCAP);
    vcnt = bit_get_field(cap, MTRRCAP_VCNT);
    pr_info("mtrr: %zu variable ranges\n", vcnt);

    for (i = 0; i < vcnt; ++i) {
        uint64_t base, mask, addr, size, type;
        char *name = "?";

        base = rdmsr(MSR_IA32_MTRR_PHYSBASE(i));
        mask = rdmsr(MSR_IA32_MTRR_PHYSMASK(i));
        if (!(mask & MTRR_PHYSMASK_VALID))
            continue;
        addr = base & MTRR_PHYSBASE_PHYSBASE;
        size = ((~((mask)&MTRR_PHYSMASK_PHYSMASK) & BITMASK64(39, 0)) + 1);
        type = base & MTRR_PHYSBASE_TYPE;
        if (type < countof(names) && names[type])
            name = names[type];
        pr_info("mtrr: 0x%016" PRIx64 "-0x%016" PRIx64 ": %s\n", addr, addr + size - 1, name);
    }
}
