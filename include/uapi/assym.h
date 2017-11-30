#pragma once

#define ASSYM_BIAS 0x10000 /* avoid zero-length arrays */
#define ASSYM_ABS(value) ((value) < 0 ? -((value) + 1) + 1ULL : (value))

#define ASSYM(name, value)                                                                         \
    char name##sign[((value) < 0 ? 1 : 0) + ASSYM_BIAS];                                           \
    char name##w0[(ASSYM_ABS(value) & 0xFFFFU) + ASSYM_BIAS];                                      \
    char name##w1[((ASSYM_ABS(value) & 0xFFFF0000UL) >> 16) + ASSYM_BIAS];                         \
    char name##w2[((ASSYM_ABS(value) & 0xFFFF00000000ULL) >> 32) + ASSYM_BIAS];                    \
    char name##w3[((ASSYM_ABS(value) & 0xFFFF000000000000ULL) >> 48) + ASSYM_BIAS]
