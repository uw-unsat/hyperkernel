#pragma once

#include <uapi/cdefs.h>

#define NR_linux_syscalls 1024
#define LINUX_read 0
#define LINUX_write 1
#define LINUX_open 2
#define LINUX_close 3
#define LINUX_stat 4
#define LINUX_fstat 5
#define LINUX_lstat 6
#define LINUX_poll 7
#define LINUX_lseek 8
#define LINUX_mmap 9
#define LINUX_mprotect 10
#define LINUX_munmap 11
#define LINUX_brk 12
#define LINUX_rt_sigaction 13
#define LINUX_rt_sigprocmask 14
#define LINUX_rt_sigreturn 15
#define LINUX_ioctl 16
#define LINUX_access 21
#define LINUX_fcntl 72
#define LINUX_unlink 87
#define LINUX_getuid 102
#define LINUX_arch_prctl 158
#define LINUX_gettid 186
#define LINUX_time 201
#define LINUX_exit_group 231
#define LINUX_newfstatat 262

/* mmap */
#define PROT_READ 0x1
#define PROT_WRITE 0x2
#define PROT_EXEC 0x4
#define PROT_NONE 0x0

#define MAP_SHARED 0x01
#define MAP_PRIVATE 0x02
#define MAP_FIXED 0x10
#define MAP_ANONYMOUS 0x20

/* rt_sigaction */
#define SIGSEGV 11

#define SA_NOCLDSTOP 0x00000001
#define SA_NOCLDWAIT 0x00000002
#define SA_SIGINFO 0x00000004
#define SA_ONSTACK 0x08000000
#define SA_RESTART 0x10000000
#define SA_NODEFER 0x40000000
#define SA_RESETHAND 0x80000000
#define SA_RESTORER 0x04000000

#define SEGV_MAPPER 1
#define SEGV_ACCERR 2

/* ioctl */
#define TCGETS 0x5401
#define TCSETSF 0x5404
#define TIOCGWINSZ 0x5413

/* arch_prctl */
#define ARCH_SET_GS 0x1001
#define ARCH_SET_FS 0x1002
#define ARCH_GET_FS 0x1003
#define ARCH_GET_GS 0x1004

#ifndef __ASSEMBLER__

#define __SI_MAX_SIZE 128
#define __SI_PAD_SIZE ((__SI_MAX_SIZE / sizeof(int)) - 4)

typedef struct {
    uintptr_t sig[1];
} sigset_t;

typedef struct {
    int si_signo;
    int si_errno;
    int si_code;

    union {
        int _pad[__SI_PAD_SIZE];

        /* SIGILL, SIGFPE, SIGSEGV, SIGBUS */
        struct {
            void *si_addr;
            short int si_addr_lsb;
            struct {
                void *_lower;
                void *_upper;
            } si_addr_bnd;
        } _sigfault;
    } _sifields;
} siginfo_t;

struct sigaction {
    void (*sa_handler)(int, siginfo_t *, void *);
    uintptr_t sa_flags;
    void (*sa_restorer)(void);
    sigset_t sa_mask;
};

struct linux_stat {
    uint64_t st_dev;
    uint64_t st_ino;
    uint64_t st_nlink;

    uint32_t st_mode;
    uint32_t st_uid;
    uint32_t st_gid;
    uint32_t __pad0;
    uint64_t st_rdev;
    int64_t st_size;
    int64_t st_blksize;
    int64_t st_blocks;

    uint64_t st_atime;
    uint64_t st_atime_nsec;
    uint64_t st_mtime;
    uint64_t st_mtime_nsec;
    uint64_t st_ctime;
    uint64_t st_ctime_nsec;
    int64_t __unused[3];
};

#define S_IFMT 0170000
#define S_IFSOCK 0140000
#define S_IFLNK 0120000
#define S_IFREG 0100000
#define S_IFBLK 0060000
#define S_IFDIR 0040000
#define S_IFCHR 0020000
#define S_IFIFO 0010000

typedef uint64_t time_t;

struct winsize {
    unsigned short ws_row;
    unsigned short ws_col;
    unsigned short ws_xpixel;   /* unused */
    unsigned short ws_ypixel;   /* unused */
};

#endif /* !__ASSEMBLER__ */
