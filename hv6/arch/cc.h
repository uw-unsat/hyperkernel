#pragma once

#include "user.h"

#define LWIP_PLATFORM_DIAG(x)                                                                      \
    do {                                                                                           \
        cprintf x;                                                                                 \
    } while (0)
#define LWIP_PLATFORM_ASSERT(x) panic(x)

#ifndef LITTLE_ENDIAN
#error LITTLE_ENDIAN not defined
#endif
#define BYTE_ORDER LITTLE_ENDIAN

#define PACK_STRUCT_STRUCT __packed

/* suppress compiler warning */
#define X8_F "02x"

#define LWIP_RAND rdtsc
