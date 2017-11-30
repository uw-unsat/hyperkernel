#pragma once

#include <stddef.h>

#define _BITSET_BITS       (sizeof(unsigned long) * 8)

#define __howmany(x, y)    (((x) + ((y) - 1)) / (y))

#define __bitset_words(_s) (__howmany(_s, _BITSET_BITS))

#define __bitset_mask(n)   (1UL << ((n) % _BITSET_BITS))

#define __bitset_word(n)   ((n) / _BITSET_BITS)

#define BITSET_DEFINE(t, _s) unsigned long t[__bitset_words(_s)]

static inline void bit_set(size_t n, unsigned long *bits)
{
    bits[__bitset_word(n)] |= __bitset_mask(n);
}

static inline void bit_clear(size_t n, unsigned long *bits)
{
    bits[__bitset_word(n)] &= ~__bitset_mask(n);
}

static inline int bit_isset(size_t n, unsigned long *bits)
{
    return !!(bits[__bitset_word(n)] & __bitset_mask(n));
}
