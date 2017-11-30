#pragma once

#include <stdint.h>

#define T_DIR 1  /* directory */
#define T_FILE 2 /* file */
#define T_DEV 3  /* device */

struct stat {
    short type;    /* type of file */
    int dev;       /* file system's disk device */
    uint32_t ino;  /* inode number */
    short nlink;   /* number of links to file */
    uint32_t size; /* size of file in bytes */
    int atime;
    int mtime;
    int ctime;
};
