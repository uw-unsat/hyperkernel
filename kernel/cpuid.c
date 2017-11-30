#include <uapi/machine/cpufunc.h>
#include "cpuid.h"

static uint32_t features[CPUID_LEAF_MAX];

void cpuid_init(void)
{
    uint32_t regs[4], highest;

    cpuid(0, regs);
    highest = regs[0];

    if (highest >= 1) {
        cpuid(1, regs);
        features[CPUID_1_EDX] = regs[3];
        features[CPUID_1_ECX] = regs[2];
    }

    if (highest >= 7) {
        cpuid2(7, 0, regs);
        features[CPUID_7_0_EBX] = regs[1];
        features[CPUID_7_0_ECX] = regs[2];
        features[CPUID_7_0_EDX] = regs[3];
    }

    cpuid(0x80000000, regs);
    highest = regs[0];

    if (highest >= 0x80000001) {
        cpuid(0x80000001, regs);
        features[CPUID_80000001_EDX] = regs[3];
        features[CPUID_80000001_ECX] = regs[2];
    }

    if (highest >= 0x8000000a) {
        cpuid(0x8000000a, regs);
        features[CPUID_8000000A_EDX] = regs[3];
    }
}

bool cpuid_has(int bit)
{
    return !!(features[bit / 32U] & (1U << (bit % 32U)));
}
