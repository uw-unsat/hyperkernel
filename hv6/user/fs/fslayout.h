#pragma once

#include <stdint.h>

#define MAXOPBLOCKS 10            /* max # of blocks any FS op writes */
#define LOGSIZE (MAXOPBLOCKS * 3) /* max data sectors in on-disk log */
#define NBUF (MAXOPBLOCKS * 3)    /* size of disk block cache */
#define HWBIGF

typedef unsigned char uchar;
typedef unsigned short ushort;
typedef unsigned int uint;

/*
 * On-disk file system format.
 * Both the kernel and user programs use this header file.
 *
 * Block 0 is unused.
 * Block 1 is super block.
 * Blocks 2 through sb.ninodes/IPB hold inodes.
 * Then free bitmap blocks holding sb.size bits.
 * Then sb.nblocks data blocks.
 * Then sb.nlog log blocks.
 */

#define ROOTINO 1  /* root i-number */
#define BSIZE 4096 /* block size */

/* file system super block */
struct superblock {
    uint size;    /* size of file system image (blocks) */
    uint nblocks; /* number of data blocks */
    uint ninodes; /* number of inodes */
    uint nlog;    /* number of log blocks */
};

#define NDIRECT 8
#define NINDIRECT (BSIZE / sizeof(uint))
#define NDINDIRECT (NINDIRECT * NINDIRECT)
#define MAXFILE (NDIRECT + NINDIRECT + NDINDIRECT)

// On-disk inode structure
struct dinode {
    short type;  /* file type */
    short major; /* major device number (T_DEV only) */
    short minor; /* minor device number (T_DEV only) */
    short nlink; /* number of links to inode in file system */
    uint size;   /* size of file (bytes) */
    int ctime;
    int atime;
    int mtime;
    uint addrs[NDIRECT + 2]; /* data block addresses */
};

/* inodes per block */
#define IPB (BSIZE / sizeof(struct dinode))

/* block containing inode i */
#define IBLOCK(i) ((i) / IPB + 2)

/* bitmap bits per block */
#define BPB (BSIZE * 8)

/* block containing bit for block b */
#define BBLOCK(b, ninodes) (b / BPB + (ninodes) / IPB + 3)

/* directory is a file containing a sequence of dirent structures */
#define DIRSIZ 62

struct dirent {
    uint16_t inum;
    char name[DIRSIZ];
};

/* in-memory copy of an inode */
struct inode {
    uint dev;  /* device number */
    uint inum; /* inode number */
    int ref;   /* reference count */
    int flags; /* I_BUSY, I_VALID */

    short type; /* copy of disk inode */
    short major;
    short minor;
    short nlink;
    uint size;
    int ctime;
    int atime;
    int mtime;
    uint addrs[NDIRECT + 2];
};

#define I_BUSY 0x1
#define I_VALID 0x2
