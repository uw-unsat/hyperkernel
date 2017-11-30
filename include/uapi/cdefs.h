#pragma once

#ifndef __ASSEMBLER__
#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdnoreturn.h>
#include <limits.h>
#else
#define UINT32_C(x) x
#define UINT64_C(x) x
#endif

/* format specifier macros (inttypes.h is not for freestanding) */
#if defined(__LP64__) || defined(_LP64)
#define __PRI64_PREFIX "l"
#else
#define __PRI64_PREFIX "ll"
#endif

#ifndef PRIx64
#define PRIx64 __PRI64_PREFIX "x"
#endif

#ifndef PRIX64
#define PRIX64 __PRI64_PREFIX "X"
#endif

#ifndef PRIu64
#define PRIu64 __PRI64_PREFIX "u"
#endif

#ifndef PRIxPTR
#define PRIxPTR "lx"
#endif

/* expand macro value */
#define __STRINGIFY(x) #x
#define STRINGIFY(x) __STRINGIFY(x)

#define NON_NULL(ptr)                                                                              \
    ({                                                                                             \
        typeof(ptr) _ptr = (ptr);                                                                  \
        (_ptr) ? (_ptr) : (panic(#ptr " NULL in " __FILE__ " on line %d", __LINE__), NULL);        \
    })

#define ERR_OK(val)                                                                                \
    ({                                                                                             \
        typeof(val) _val = (val);                                                                  \
        (_val) ? (panic(#val " non-zero in " __FILE__ " on line %d", __LINE__), -1) : (_val);      \
    })

/* bit macros */
#define BIT32(n) (UINT32_C(1) << (n))
#define BIT64(n) (UINT64_C(1) << (n))
#define __BITS32(h, l) (((BIT32((h) - (l)) << 1) - 1) << (l))
#define __BITS64(h, l) (((BIT64((h) - (l)) << 1) - 1) << (l))
#define BITS32(h, l) __BITS32(max(h, l), min(h, l))
#define BITS64(h, l) __BITS64(max(h, l), min(h, l))
#define BITMASK32(h, l) BITS32(h, l)
#define BITMASK64(h, l) BITS64(h, l)

#define __LOWEST_SET_BIT(mask) ((((mask)-1) & (mask)) ^ (mask))
#define __SHIFTOUT(x, mask) (((x) & (mask)) / __LOWEST_SET_BIT(mask))
#define __SHIFTIN(x, mask) ((x)*__LOWEST_SET_BIT(mask))
#define __BIT BIT32
#define __BITS BITS32

#define bit_get_field(val, fieldkey)                                                               \
    ({                                                                                             \
        typeof(val) _val = val;                                                                    \
        typeof(fieldkey) _fieldkey = fieldkey;                                                     \
        (_val & _fieldkey) / (_fieldkey & ~(_fieldkey - 1));                                       \
    })

#define bit_set_field(val, fieldkey, fieldval)                                                     \
    ({                                                                                             \
        typeof(val) _val = val;                                                                    \
        typeof(fieldkey) _fieldkey = fieldkey;                                                     \
        typeof(fieldval) _fieldval = fieldval;                                                     \
        (_val & ~_fieldkey) | (_fieldval * (_fieldkey & ~(_fieldkey - 1)));                        \
    })

/* sizes */
#define SZ_1K UINT64_C(0x00000400)
#define SZ_4K UINT64_C(0x00001000)
#define SZ_64K UINT64_C(0x00010000)
#define SZ_1M UINT64_C(0x00100000)
#define SZ_2M UINT64_C(0x00200000)
#define SZ_4M UINT64_C(0x00400000)
#define SZ_8M UINT64_C(0x00800000)
#define SZ_16M UINT64_C(0x01000000)
#define SZ_32M UINT64_C(0x02000000)
#define SZ_64M UINT64_C(0x04000000)
#define SZ_512M UINT64_C(0x20000000)
#define SZ_1G UINT64_C(0x40000000)
#define SZ_2G UINT64_C(0x80000000)
#define SZ_4G UINT64_C(0x0000000100000000)
#define SZ_512G UINT64_C(0x0000008000000000)
#define SZ_1T UINT64_C(0x0000010000000000)
#define SZ_256T UINT64_C(0x0001000000000000)

#ifdef __ASSEMBLER__
#define UINTPTR_T(x) (x)
#else
#define UINTPTR_T(x) ((uintptr_t)(x))
#endif

#ifndef __ASSEMBLER__

#define static_assert _Static_assert

/* attributes */
#define __aligned(alignment) __attribute__((aligned(alignment)))
/* __always_inline may be defined in standard headers */
#ifdef __always_inline
#undef __always_inline
#endif
#define __always_inline inline __attribute__((always_inline))
#define __packed __attribute__((packed))
#define __printf(stri, firsti) __attribute__((format(printf, stri, firsti)))
#define __section(name) __attribute__((section(#name)))
/* __weak may be defined by clang */
#ifdef __weak
#undef __weak
#endif
#define __weak __attribute__((weak))

/* common macros/functions */
#define countof(a)                                                                                 \
    ({                                                                                             \
        static_assert(!__builtin_types_compatible_p(typeof(a), typeof(&a[0])),                     \
                      "must be used with an array");                                               \
        (sizeof(a) / sizeof((a)[0]));                                                              \
    })

#define min(a, b)                                                                                  \
    ({                                                                                             \
        static_assert(__builtin_types_compatible_p(typeof(a), typeof(b)),                          \
                      "must be the same type");                                                    \
        typeof(a) _a = (a);                                                                        \
        typeof(b) _b = (b);                                                                        \
        _a <= _b ? _a : _b;                                                                        \
    })

#define max(a, b)                                                                                  \
    ({                                                                                             \
        static_assert(__builtin_types_compatible_p(typeof(a), typeof(b)),                          \
                      "must be the same type");                                                    \
        typeof(a) _a = (a);                                                                        \
        typeof(b) _b = (b);                                                                        \
        _a >= _b ? _a : _b;                                                                        \
    })

#define roundup(x, y)                                                                              \
    ({                                                                                             \
        uintmax_t _x = (uintmax_t)(x);                                                             \
        const typeof(y) _y = y;                                                                    \
        (typeof(x))((((_x) + (_y - 1)) / _y) * _y);                                                \
    })

#define rounddown(x, y)                                                                            \
    ({                                                                                             \
        uintmax_t _x = (uintmax_t)(x);                                                             \
        const typeof(y) _y = y;                                                                    \
        (typeof(x))(((_x) / _y) * _y);                                                             \
    })

#define ALIGN(x, a) ALIGN_MASK(x, (typeof(x))(a) - 1)
#define ALIGN_MASK(x, mask) (((x) + (mask)) & ~(mask))

/* types */
typedef intptr_t ssize_t;
typedef uintptr_t physaddr_t;
typedef uintptr_t register_t;
typedef uint32_t pagecount_t;
typedef uint32_t timer_t;
typedef int64_t pid_t;

#define TIMER_MAX UINT32_MAX

#define pa2kva(x) ((void *)(uintptr_t)(x))
#define kva2pa(x) ((physaddr_t)(x))

#define assert(exp, fmt, ...)                                                                      \
    ({                                                                                             \
        if (!(exp))                                                                                \
            panic("%s:%d: %s: assert failed: " fmt, __FILE__, __LINE__, __func__, ##__VA_ARGS__);  \
    })

#define LOG_EMERG 0
#define LOG_ALERT 1
#define LOG_CRIT 2
#define LOG_ERR 3
#define LOG_WARNING 4
#define LOG_NOTICE 5
#define LOG_INFO 6
#define LOG_DEBUG 7

#define pr_emerg(fmt, ...) syslog(LOG_EMERG, fmt, ##__VA_ARGS__)
#define pr_alert(fmt, ...) syslog(LOG_ALERT, fmt, ##__VA_ARGS__)
#define pr_crit(fmt, ...) syslog(LOG_CRIT, fmt, ##__VA_ARGS__)
#define pr_err(fmt, ...) syslog(LOG_ERR, fmt, ##__VA_ARGS__)
#define pr_warn(fmt, ...) syslog(LOG_WARNING, fmt, ##__VA_ARGS__)
#define pr_notice(fmt, ...) syslog(LOG_NOTICE, fmt, ##__VA_ARGS__)
#define pr_info(fmt, ...) syslog(LOG_INFO, fmt, ##__VA_ARGS__)
#define pr_debug(fmt, ...) syslog(LOG_DEBUG, fmt, ##__VA_ARGS__)

#define KLOG_NR_LINES  SZ_1K
#define KLOG_LINE_SIZE 256

noreturn void panic(const char *fmt, ...) __printf(1, 2);
void syslog(int priority, const char *fmt, ...) __printf(2, 3);
void vsyslog(int priority, const char *fmt, va_list ap) __printf(2, 0);
int syslog_read(void *dest, size_t n, size_t offset);

#endif /* !__ASSEMBLER__ */
