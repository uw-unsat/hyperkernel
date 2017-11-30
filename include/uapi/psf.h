#pragma once

#include <uapi/cdefs.h>

#define PSF2_MAGIC0     0x72
#define PSF2_MAGIC1     0xb5
#define PSF2_MAGIC2     0x4a
#define PSF2_MAGIC3     0x86

/* bits used in flags */
#define PSF2_HAS_UNICODE_TABLE 0x01

/* max version recognized so far */
#define PSF2_MAXVERSION 0

/* UTF8 separators */
#define PSF2_SEPARATOR  0xFF
#define PSF2_STARTSEQ   0xFE

struct psf2_header {
        unsigned char magic[4];
        unsigned int version;
        unsigned int headersize;    /* offset of bitmaps in file */
        unsigned int flags;
        unsigned int length;        /* number of glyphs */
        unsigned int charsize;      /* number of bytes for each character */
        unsigned int height, width; /* max dimensions of glyphs */
        /* charsize = height * ((width + 7) / 8) */
} __packed;
