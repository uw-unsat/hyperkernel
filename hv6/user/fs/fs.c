#include <uapi/machine/io.h>
#include <uapi/console.h>
#include "fs.h"

typedef int (*handler_t)(pid_t);

static int do_open(pid_t);
static int do_pread(pid_t);
static int do_mknod(pid_t);
static int do_fstat(pid_t);
static int do_pwrite(pid_t);
static int do_mkdir(pid_t);
static int do_unlink(pid_t);
static int do_pipe(pid_t);
static int do_membuf(pid_t);

static handler_t handlers[] = {
        [FSIPC_OPEN] = do_open,     [FSIPC_PREAD] = do_pread, [FSIPC_MKNOD] = do_mknod,
        [FSIPC_MKDIR] = do_mkdir,   [FSIPC_FSTAT] = do_fstat, [FSIPC_PWRITE] = do_pwrite,
        [FSIPC_UNLINK] = do_unlink, [FSIPC_PIPE] = do_pipe,   [FSIPC_MEMBUF] = do_membuf,
};

struct devsw devsw[NDEV];

extern char _binary_fs_img_start[], _binary_fs_img_end[];

static uint8_t ping_buf[PAGE_SIZE] __aligned(PAGE_SIZE);
static uint8_t pong_buf[PAGE_SIZE] __aligned(PAGE_SIZE);
static struct fsipc_ping *ping = (void *)ping_buf;
static struct fsipc_pong *pong = (void *)pong_buf;

static void consoleinit(void);
static void gc(void);
static struct file *fd_lookup(pid_t pid, int fd);

noreturn void fs_main(void)
{
    struct superblock sb;
    int r;

    set_proc_name("fs");

    unix_init();
    consoleinit();
    binit();
    initlog();

    readsb(ROOTDEV, &sb);
    cprintf("fs: size %d nblocks %d ninodes %d nlog %d\n", sb.size, sb.nblocks, sb.ninodes,
            sb.nlog);

    r = sys_recv(INITPID, virt_to_pn(ping), -1);
    while (1) {
        if (r == 0) {
            size_t op = ucurrent->ipc_val;

            if (op < countof(handlers)) {
                handler_t handler;

                handler = handlers[op];
                if (handler) {
                    gc();
                    r = handler(ucurrent->ipc_from);
                    continue;
                }
            }
        }
        r = sys_recv(INITPID, virt_to_pn(ping), -1);
    }
    exit();
}

static int do_open(pid_t pid)
{
    struct file *cwd;
    int fd, r;

    cwd = fd_lookup(ucurrent->ipc_from, ping->open.dirfd);
    fd = fileopen(cwd, ping->open.path, ping->open.omode);
    r = (fd < 0) ? fd : 0;
    return sys_reply_wait(pid, r, virt_to_pn(pong), 0, fd, virt_to_pn(ping));
}

static int do_pread(pid_t pid)
{
    struct file *f;
    size_t count;
    ssize_t r;

    f = fd_lookup(ucurrent->ipc_from, ping->pread.fd);
    count = min(ping->pread.count, PAGE_SIZE);
    r = filepread(f, (void *)pong, count, ping->pread.offset);
    return sys_reply_wait(pid, r, virt_to_pn(pong), (r > 0) ? r : 0, -1, virt_to_pn(ping));
}

static int do_mknod(pid_t pid)
{
    struct file *cwd;
    int r;

    cwd = fd_lookup(ucurrent->ipc_from, ping->mknod.dirfd);
    r = filemknod(cwd, ping->mknod.path, ping->mknod.major, ping->mknod.minor);
    return sys_reply_wait(pid, r, virt_to_pn(pong), 0, -1, virt_to_pn(ping));
}

static int do_mkdir(pid_t pid)
{
    struct file *cwd;
    int r;

    cwd = fd_lookup(ucurrent->ipc_from, ping->mkdir.dirfd);
    r = filemkdir(cwd, ping->mkdir.path);
    return sys_reply_wait(pid, r, virt_to_pn(pong), 0, -1, virt_to_pn(ping));
}

static int do_fstat(pid_t pid)
{
    struct file *f;
    ssize_t r;
    f = fd_lookup(ucurrent->ipc_from, ping->fstat.fd);
    r = filestat(f, (struct stat *)pong);
    return sys_reply_wait(pid, r, virt_to_pn(pong), (r == 0) ? sizeof(struct stat) : 0, -1,
                          virt_to_pn(ping));
}

static int do_pwrite(pid_t pid)
{
    struct file *f;
    size_t count;
    ssize_t r;

    f = fd_lookup(ucurrent->ipc_from, ping->pread.fd);
    count = min(ping->pwrite.count, sizeof(ping->pwrite.buf));
    r = filepwrite(f, ping->pwrite.buf, count, ping->pread.offset);
    return sys_reply_wait(pid, r, virt_to_pn(pong), 0, -1, virt_to_pn(ping));
}

static int do_unlink(pid_t pid)
{
    struct file *cwd;
    int r;

    cwd = fd_lookup(ucurrent->ipc_from, ping->unlink.dirfd);
    r = fileunlink(cwd, ping->unlink.path);
    return sys_reply_wait(pid, r, virt_to_pn(pong), 0, -1, virt_to_pn(ping));
}

static int do_pipe(pid_t pid)
{
    int fds[2], r;

    r = pipealloc(fds);
    assert(r == 0, "pipealloc");
    /* send two file descriptors */
    r = sys_send(pid, r, virt_to_pn(pong), 0, fds[0]);
    assert(r == 0, "sys_send");
    while (uprocs[pid].state != PROC_SLEEPING)
        yield();
    return sys_reply_wait(pid, r, virt_to_pn(pong), 0, fds[1], virt_to_pn(ping));
}

static int do_membuf(pid_t pid)
{
    int r;

    r = membuf_get(pong);
    return sys_reply_wait(pid, r, virt_to_pn(pong), 80 * 25, -1, virt_to_pn(ping));
}

static struct file *fd_lookup(pid_t pid, int fd)
{
    fn_t fn;

    if (!is_fd_valid(fd))
        return 0;
    fn = uprocs[pid].ofile[fd];
    if (!is_fn_valid(fn))
        return 0;
    /* TODO: check own ofile for fd */
    return &ufiles[fn];
}

int unix_time(void)
{
    return 0;
}

static int consoleread(struct inode *ip, char *buf, size_t count, size_t offset)
{
    int r;

    r = console_getc();
    if (r == 0)
        return -EAGAIN;

    buf[0] = r;
    return 1;
}

static int enable_cga = ENABLED(CONFIG_CGA);

static int consolewrite(struct inode *ip, char *buf, size_t count)
{
    if (enable_cga)
        debug_print_screen(buf, count);
    console_write(buf, count);
    return count;
}

static void consoleinit(void)
{
    /* enable I/O ports */
    alloc_ports(PORT_COM1, 6);
    alloc_port(PORT_KBD_DATA);
    alloc_port(PORT_KBD_STATUS);
    alloc_ports(PORT_CRT, 2);

    /* initialize user console */
    uart8250_init();
    kbd_init();
    membuf_init();

    devsw[DEV_CONSOLE].write = consolewrite;
    devsw[DEV_CONSOLE].read = consoleread;

    if (is_kvm())
        enable_cga = 0;
}

/* reclaim fds */
static void gc(void)
{
    int fd;
    fn_t fn;
    struct file *f;

    for (fd = 0; fd < NOFILE; ++fd) {
        fn = ucurrent->ofile[fd];

        if (!is_fn_valid(fn))
            continue;
        f = &ufiles[fn];
        if (f->refcnt != 1)
            continue;
        if (f->type == FD_PIPE)
            pipeclose(file_pipe(f), file_writable(f));
        close(fd);
    }
}
