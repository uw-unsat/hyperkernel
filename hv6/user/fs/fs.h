#pragma once

#include "fslayout.h"
#include "user.h"

#define NINODE 100 /* maximum number of active i-nodes */
#define NDEV 10    /* maximum major device number */
#define ROOTDEV 1  /* device number of file system root disk */

enum {
    FSIPC_OPEN = 1,
    FSIPC_PREAD,
    FSIPC_MKNOD,
    FSIPC_MKDIR,
    FSIPC_FSTAT,
    FSIPC_PWRITE,
    FSIPC_UNLINK,
    FSIPC_PIPE,
    FSIPC_MEMBUF,
};

struct fsipc_ping {
    union {
        struct {
            int dirfd;
            char path[MAXPATH];
            int omode;
        } open;
        struct {
            int fd;
            size_t count;
            off_t offset;
        } pread;
        struct {
            int dirfd;
            char path[MAXPATH];
            short major;
            short minor;
        } mknod;
        struct {
            int dirfd;
            char path[MAXPATH];
            int mode;
        } mkdir;
        struct {
            int fd;
        } fstat;
        struct {
            int fd;
            size_t count;
            off_t offset;
            char buf[PAGE_SIZE - 24];
        } pwrite;
        struct {
            int dirfd;
            char path[MAXPATH];
            int flags;
        } unlink;
    };
};

struct fsipc_pong {
};

/* table mapping major device number to device functions */
struct devsw {
    int (*read)(struct inode *, char *, size_t n, size_t off);
    int (*write)(struct inode *, char *, size_t n);
};

extern struct devsw devsw[];

struct pipe;

struct buf {
    int flags;
    uint dev;
    uint sector;
    struct buf *prev; /* LRU cache list */
    struct buf *next;
    struct buf *qnext; /* disk queue */
    uint8_t data[BSIZE];
};

#define B_BUSY 0x1  /* buffer is locked by some process */
#define B_VALID 0x2 /* buffer has been read from disk */
#define B_DIRTY 0x4 /* buffer needs to be written to disk */

struct spinlock {
    int locked;
};

static inline void initlock(struct spinlock *lk, char *name)
{
}
static inline void acquire(struct spinlock *lk)
{
}
static inline void release(struct spinlock *lk)
{
}
static inline void sleep(void *addr, struct spinlock *lk)
{
}
static inline void wakeup(void *addr)
{
}

void unix_init(void);
void unix_read(uint64_t block, void *buf);
void unix_write(uint64_t block, const void *buf);
void unix_flush(void);
int unix_time(void);

/* bio.c */
void binit(void);
struct buf *bread(uint, uint);
void brelse(struct buf *);
void bwrite(struct buf *);

/* ide.c */
void iderw(struct buf *);
void ideflush(void);

/* file.c */
int fileopen(struct file *cwd, char *path, int omode);
int filepread(struct file *f, char *addr, size_t count, size_t offset);
int filemknod(struct file *cwd, char *path, short major, short minor);
int filemkdir(struct file *cwd, char *path);
int filestat(struct file *f, struct stat *st);
int filepwrite(struct file *f, char *addr, size_t count, size_t offset);
int fileunlink(struct file *cwd, char *path);

static inline int file_readable(struct file *f)
{
    return !(f->omode & O_WRONLY);
}

static inline int file_writable(struct file *f)
{
    return (f->omode & O_WRONLY) || (f->omode & O_RDWR);
}

static inline struct inode *file_ip(struct file *f)
{
    return (void *)(uintptr_t)f->value;
}

static inline struct pipe *file_pipe(struct file *f)
{
    return (void *)(uintptr_t)f->value;
}

/* fs.c */
void readsb(int dev, struct superblock *sb);
int dirlink(struct inode *, char *, uint);
struct inode *dirlookup(struct inode *, char *, uint *);
struct inode *ialloc(uint, short);
struct inode *idup(struct inode *);
void ilock(struct inode *);
void iput(struct inode *);
void iunlock(struct inode *);
void iunlockput(struct inode *);
void iupdate(struct inode *);
void itrunc(struct inode *);
int namecmp(const char *, const char *);
struct inode *namei(struct file *, char *);
struct inode *nameiparent(struct file *, char *, char *);
int readi(struct inode *, char *, uint, uint);
void stati(struct inode *, struct stat *);
int writei(struct inode *, char *, uint, uint);
void zeroi(struct inode *ip, uint off, uint n);

/* log.c */
void initlog(void);
void log_write(struct buf *);
void begin_op();
void end_op();

/* pipe.c */
int pipealloc(int fds[2]);
void pipeclose(struct pipe *, int);
int piperead(struct pipe *, char *addr, int);
int pipewrite(struct pipe *, char *addr, int);
