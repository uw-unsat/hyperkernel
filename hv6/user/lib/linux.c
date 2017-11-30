#include "linux.h"
#include "user.h"

extern void linux_syscall_entry(void);

static struct sigaction act_pf;

void linux_init(void)
{
    map_pages(USYSCALL_START, PAGE_SIZE, PTE_P | PTE_W);
    memcpy((void *)USYSCALL_START, linux_syscall_entry, PAGE_SIZE);

    /* enable access to fs/gs segment base */
    lcr4(rcr4() | CR4_FSGSBASE);
}

static int linux_nop(void)
{
    cprintf("unimplemented syscall\n");
    return -ENOSYS;
}

static void *linux_mmap(void *addr, size_t length, int prot, int flags, int fd, off_t offset)
{
    uintptr_t cur;

    assert(addr == NULL, "TBD");
    if (!(flags & MAP_ANONYMOUS))
        assert(fd < 0, "TBD");
    assert(offset == 0, "TBD");
    assert(prot == (PROT_READ | PROT_WRITE), "TBD");
    assert(flags == (MAP_PRIVATE | MAP_ANONYMOUS), "TBD");

    /* abuse sbrk to avoid finding free va; no munmap */
    cur = (uintptr_t)sbrk(0);
    /* align program break to page */
    if (cur % PAGE_SIZE)
        sbrk(roundup(cur, PAGE_SIZE) - cur);
    return sbrk(length);
}

static int linux_mprotect(void *addr, size_t len, int prot)
{
    int perm = 0;

    assert((uintptr_t)addr % PAGE_SIZE == 0, "addr must be page-aligned");
    assert(prot & PROT_READ, "must be readable");
    assert((prot & ~(PROT_READ | PROT_WRITE)) == 0, "TBD");

    if (prot & PROT_READ)
        perm |= PTE_P;
    if (prot & PROT_WRITE)
        perm |= PTE_W;

    protect_pages((uintptr_t)addr, len, perm);
    return 0;
}

/*
 * sys_brk on Linux is different from the libc function:
 * - return the new program break on success;
 * - return the current break on failure.
 */
static void *linux_brk(void *addr)
{
    void *cur;

    cur = sbrk(0);
    if (addr < (void *)UBRK_START)
        return cur;
    sbrk(addr - cur);
    return addr;
}

static void pf_handler(struct trap_frame *tf)
{
    siginfo_t info = {
        .si_signo = SIGSEGV, .si_code = SEGV_ACCERR, ._sifields._sigfault.si_addr = (void *)rcr2(),
    };

    if (act_pf.sa_handler) {
        act_pf.sa_handler(SIGSEGV, &info, NULL);
    }

    /* no need to call restorer; just directly return */
}

static int linux_rt_sigaction(int sig, const struct sigaction *act, struct sigaction *oact,
                              size_t sigsetsize)
{
    assert(act, "TBD");
#if 0
	assert(oact == NULL, "TBD");
	assert(act->sa_flags == (SA_RESTORER|SA_SIGINFO), "TBD");
#endif

    switch (sig) {
    case SIGSEGV:
        register_trap_handler(TRAP_PF, pf_handler);
        if (oact)
            memcpy(oact, &act_pf, sizeof(struct sigaction));
        memcpy(&act_pf, act, sizeof(struct sigaction));
        break;
    default:
        cprintf("unimplemented sigaction: %d\n", sig);
        return -EINVAL;
    }

    return 0;
}

static int linux_arch_prctl(int code, uintptr_t addr)
{
    switch (code) {
    case ARCH_SET_FS:
        asm volatile("wrfsbase %0" : : "r"(addr));
        break;
    default:
        assert(false, "unknown code");
    }
    return 0;
}

static int linux_access(const char *path, int mode)
{
    struct stat st;
    int r;

    r = stat(path, &st);
    if (r < 0)
        return r;
    return 0;
}

static int linux_fcntl(int fd, int cmd, ...)
{
    return -EINVAL;
}

static int linux_ioctl(int fd, int request)
{
    struct stat st = {0};
    int r;

    switch (request) {
    case TCGETS:
        /*
         * This is mostly for isatty: we just return 0;
         * it's okay to not fill in the terminal information
         * or return the "right" errno.
         */
        r = fstat(fd, &st);
        if (r == 0 && st.type == T_DEV)
            return 0;
        return -1;
    case TCSETSF:
        /* ignore for now */
        return 0;
    default:
        cprintf("unimplemented ioctl: 0x%x\n", request);
        return -EINVAL;
    }
    assert(false, "unknown request");
}

int linux_getuid(void)
{
    return 0;
}

static time_t linux_time(time_t *tloc)
{
    time_t t = sys_now();

    if (tloc)
        *tloc = t;
    return t;
}

static void convert_stat(struct linux_stat *statbuf, struct stat *st)
{
    memset(statbuf, 0, sizeof(*statbuf));
    statbuf->st_dev = st->dev;
    statbuf->st_ino = st->ino;
    statbuf->st_nlink = st->nlink;
    statbuf->st_size = st->size;
    switch (st->type) {
    case T_DIR:
        statbuf->st_mode = S_IFDIR | 0777;
        break;
    case T_FILE:
        statbuf->st_mode = S_IFREG | 0666;
        break;
    case T_DEV:
        statbuf->st_mode = S_IFCHR | 0666;
        break;
    default:
        break;
    }
}

static int linux_newfstatat(int dfd, const char *filename, struct linux_stat *statbuf, int flag)
{
    int r;
    struct stat st;

    r = fstatat(dfd, filename, &st);
    if (r < 0)
        return r;
    convert_stat(statbuf, &st);
    return 0;
}

static int linux_fstat(int fd, struct linux_stat *statbuf)
{
    int r;
    struct stat st;

    r = fstat(fd, &st);
    if (r < 0)
        return r;
    convert_stat(statbuf, &st);
    return 0;
}

void *linux_syscalls[NR_linux_syscalls] = {
        [0 ... NR_linux_syscalls - 1] = linux_nop,
        [LINUX_read] = read,
        [LINUX_write] = write,
        [LINUX_open] = open,
        [LINUX_close] = close,
        [LINUX_fstat] = linux_fstat,
        [LINUX_mmap] = linux_mmap,
        [LINUX_mprotect] = linux_mprotect,
        [LINUX_brk] = linux_brk,
        [LINUX_rt_sigaction] = linux_rt_sigaction,
        [LINUX_ioctl] = linux_ioctl,
        [LINUX_access] = linux_access,
        [LINUX_fcntl] = linux_fcntl,
        [LINUX_unlink] = unlink,
        [LINUX_getuid] = linux_getuid,
        [LINUX_arch_prctl] = linux_arch_prctl,
        [LINUX_gettid] = getpid,
        [LINUX_time] = linux_time,
        [LINUX_exit_group] = exit,
        [LINUX_newfstatat] = linux_newfstatat,
};
