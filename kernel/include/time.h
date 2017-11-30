#pragma once

#include <uapi/cdefs.h>

#define NSEC_PER_SEC UINT64_C(1000000000)
#define FSEC_PER_SEC UINT64_C(1000000000000000)
#define FSEC_PER_NSEC (FSEC_PER_SEC / NSEC_PER_SEC)

typedef uint64_t seconds_t;
typedef uint64_t nanoseconds_t;
typedef uint64_t milliseconds_t;
typedef uint64_t cycle_t;

nanoseconds_t cycles_to_ns(cycle_t cycle);
cycle_t ns_to_cycles(nanoseconds_t ns);
cycle_t ms_to_cycles(milliseconds_t ms);

nanoseconds_t uptime(void);
void nanodelay(nanoseconds_t delay);
