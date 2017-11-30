#pragma once

#include <uapi/cdefs.h>

/* little endian, "EXOV" */
#define IMAGE_MAGIC 0x564f5845
#define IMAGE_TEXT_OFFSET_DEFAULT 0x00400000

#ifndef __ASSEMBLER__

/* header for init */
struct image {
    uint64_t code;
    uint64_t text_offset;
    uint64_t image_size;
    uint64_t res[4];
    uint32_t magic;
    uint32_t res5;
    uint8_t payload[];
} __packed;

#endif /* !__ASSEMBLER__ */
