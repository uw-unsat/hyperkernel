#include "fs.h"
#include "socket.h"
#include "user.h"

static int cwd_fd = -1;
static uint8_t ping_buf[PAGE_SIZE] __aligned(PAGE_SIZE);
static uint8_t pong_buf[PAGE_SIZE] __aligned(PAGE_SIZE);
static struct fsipc_ping *ping = (void *)ping_buf;
static struct fsipc_pong *pong = (void *)pong_buf;

int chdir(const char *path)
{
    assert(false, "TBD");
}

int close(int fd)
{
    int r;

    assert(is_fd_valid(fd), "fd must be valid: %d", fd);
    r = sys_close(getpid(), fd);
    assert(r == 0, "sys_close");
    return r;
}

int dup(int fd)
{
    int newfd, r;

    assert(ucurrent->ofile[fd], "fd must be valid");
    newfd = find_lowest_free_fd();
    r = sys_dup(fd, getpid(), newfd);
    assert(r == 0, "sys_dup");
    return newfd;
}

int dup2(int oldfd, int newfd)
{
    int r;

    r = sys_dup2(oldfd, getpid(), newfd);
    assert(r == 0, "sys_dup2");
    return newfd;
}

int fchdir(int fd)
{
    if (is_fd_valid(cwd_fd)) {
        /* normal case */
        dup2(fd, cwd_fd);
    } else {
        /* initialization: use higher fds */
        cwd_fd = find_free_fd(NOFILE / 2);
        dup2(fd, cwd_fd);
    }
    return 0;
}

int fstat(int fd, struct stat *st)
{
    int r;

    ping->fstat.fd = fd;
    r = sys_call(FSPID, FSIPC_FSTAT, virt_to_pn(ping), sizeof(ping->fstat), virt_to_pn(pong), -1);
    assert(r == 0, "sys_call");
    r = (int)ucurrent->ipc_val;

    if (r == 0)
        memcpy(st, pong, sizeof(struct stat));

    return r;
}

int fstatat(int dirfd, const char *pathname, struct stat *st)
{
    int fd, r;

    fd = openat(dirfd, pathname, O_RDONLY);
    if (fd < 0)
        return fd;
    r = fstat(fd, st);
    close(fd);
    return r;
}

int isatty(int fd)
{
    struct stat st = {0};
    int r;

    r = fstat(fd, &st);
    if (r < 0)
        return r;
    if (st.type == T_DEV)
        return 1;
    return 0;
}

int mkdir(const char *path, int mode)
{
    int r;

    ping->mkdir.dirfd = cwd_fd;
    strcpy(ping->mkdir.path, path);
    ping->mkdir.mode = mode;
    r = sys_call(FSPID, FSIPC_MKDIR, virt_to_pn(ping), sizeof(ping->mkdir), virt_to_pn(pong), -1);
    assert(r == 0, "sys_call");
    r = (int)ucurrent->ipc_val;
    return r;
}

int mknod(const char *path, short major, short minor)
{
    int r;

    ping->mknod.dirfd = cwd_fd;
    strcpy(ping->mknod.path, path);
    ping->mknod.major = major;
    ping->mknod.minor = minor;
    r = sys_call(FSPID, FSIPC_MKNOD, virt_to_pn(ping), sizeof(ping->mknod), virt_to_pn(pong), -1);
    assert(r == 0, "sys_call");
    r = (int)ucurrent->ipc_val;
    return r;
}

int openat(int dirfd, const char *path, int omode)
{
    int r, fd;

    ping->open.dirfd = dirfd;
    strcpy(ping->open.path, path);
    ping->open.omode = omode;
    fd = find_lowest_free_fd();
    while (1) {
        r = sys_call(FSPID, FSIPC_OPEN, virt_to_pn(ping), sizeof(ping->open), virt_to_pn(pong), fd);
        if (r != -EAGAIN)
            break;
        yield();
    }
    assert(r == 0, "sys_call");
    r = (int)ucurrent->ipc_val;
    if (r < 0)
        return r;
    assert(is_fn_valid(ucurrent->ofile[fd]), "must be valid file");
    return fd;
}

int open(const char *path, int omode)
{
    return openat(cwd_fd, path, omode);
}

int getchar(int fd)
{
    uint8_t c;
    ssize_t r;

    r = read(fd, &c, 1);
    if (r < 0)
        return r;
    return c;
}

int pipe(int fds[2])
{
    int r, fd0, fd1;

    fd0 = find_lowest_free_fd();
    fd1 = find_free_fd(fd0 + 1);
    r = sys_call(FSPID, FSIPC_PIPE, virt_to_pn(ping), 0, virt_to_pn(pong), fd0);
    assert(r == 0 && ucurrent->ipc_val == 0, "sys_call");
    r = sys_recv(FSPID, virt_to_pn(ping), fd1);
    assert(r == 0 && ucurrent->ipc_val == 0, "sys_recv");
    assert(ucurrent->ipc_from == FSPID, "must be from fs");
    assert(fd_to_file(fd0)->type == FD_PIPE, "fd0 must be pipe");
    assert(fd_to_file(fd1)->type == FD_PIPE, "fd1 must be pipe");
    fds[0] = fd0;
    fds[1] = fd1;
    return r;
}

void *membuf(int *pos)
{
    int r;

    r = sys_call(FSPID, FSIPC_MEMBUF, virt_to_pn(ping), 0, virt_to_pn(pong), -1);
    assert(r == 0, "sys_call");
    *pos = (int)ucurrent->ipc_val;
    return pong;
}

static ssize_t pread0(int fd, void *buf, size_t len, off_t offset)
{
    void *dst;
    ssize_t r;

    ping->pread.fd = fd;
    ping->pread.count = len;
    ping->pread.offset = offset;
    /* avoid one copy if buf is page-aligned */
    dst = ((uintptr_t)buf % PAGE_SIZE) ? pong : buf;
    while (1) {
        r = sys_call(FSPID, FSIPC_PREAD, virt_to_pn(ping), sizeof(ping->pread), virt_to_pn(dst),
                     -1);
        if (r == -EAGAIN) {
            yield();
            continue;
        }
        assert(r == 0, "sys_call");
        break;
    }
    r = ucurrent->ipc_val;
    /* extra copy if buf is not page-aligned */
    if (r > 0 && dst != buf)
        memcpy(buf, dst, r);
    return r;
}

ssize_t pread(int fd, void *buf, size_t len, off_t offset)
{
    ssize_t r, nbytes = 0;
    int tty = isatty(fd);

    while (len) {
        r = pread0(fd, buf, len, offset);
        if (r == -EAGAIN) {
            yield();
            continue;
        }
        assert(r >= 0, "pread0");
        if (r == 0)
            break;
        buf += r;
        len -= r;
        offset += r;
        nbytes += r;
        /* for tty: don't buffer */
        if (tty)
            break;
    }

#if 0
    /* echo if tty */
    if (tty && nbytes > 0) {
        size_t i;

        buf -= nbytes;
        for (i = 0; i < nbytes; ++i) {
            switch (buf[i]) {
            default:
                break;
            case '\r':
                buf[i] = '\n';
                break;
            }
            putchar(fd, *buf);
        }
    }
#endif

    return nbytes;
}

static ssize_t pwrite0(int fd, const void *buf, size_t len, off_t offset)
{
    ssize_t r;

    if (fd_to_file(fd)->type == FD_SOCKET)
        return send(fd, buf, len, 0);

    ping->pwrite.fd = fd;
    ping->pwrite.count = len;
    ping->pwrite.offset = offset;
    len = min(len, sizeof(ping->pwrite.buf));
    memcpy(ping->pwrite.buf, buf, len);
    while (1) {
        r = sys_call(FSPID, FSIPC_PWRITE, virt_to_pn(ping), sizeof(ping->pwrite), virt_to_pn(pong),
                     -1);
        if (r == -EAGAIN) {
            yield();
            continue;
        }
        assert(r == 0, "sys_call");
        break;
    }
    r = ucurrent->ipc_val;
    return r;
}

ssize_t pwrite(int fd, const void *buf, size_t len, off_t offset)
{
    ssize_t r, nbytes = 0;

    while (len) {
        r = pwrite0(fd, buf, len, offset);
        if (r == -EAGAIN) {
            yield();
            continue;
        }
        assert(r >= 0, "pwrite0");
        if (r == 0)
            break;
        buf += r;
        len -= r;
        offset += r;
        nbytes += r;
    }

    return nbytes;
}

int putchar(int fd, uint8_t c)
{
    ssize_t r;

    /* for debugging */
    if (fd < 0) {
        debug_print_console(&c, 1);
        return 0;
    }

    r = write(fd, &c, 1);
    if (r < 0)
        return r;
    return 0;
}

ssize_t read(int fd, void *buf, size_t len)
{
    struct file *file;
    off_t offset = 0;
    ssize_t n;
    bool seekable = false;

    file = fd_to_file(fd);
    if (file->type == FD_INODE) {
        seekable = true;
        offset = file->offset;
    }

    n = pread(fd, buf, len, offset);

    /* bump the offset */
    if (seekable && n > 0) {
        int r;

        r = sys_lseek(fd, offset + n);
        assert(r == 0, "sys_lseek");
    }
    return n;
}

int stat(const char *path, struct stat *st)
{
    int fd, r;

    fd = open(path, O_RDONLY);
    if (fd < 0)
        return fd;
    r = fstat(fd, st);
    close(fd);
    return r;
}

ssize_t write(int fd, const void *buf, size_t len)
{
    struct file *file;
    off_t offset = 0;
    ssize_t nbytes;
    bool seekable = false;
    int r;

    file = fd_to_file(fd);
    if (file->type == FD_INODE) {
        offset = file->offset;
        seekable = true;
    }
    nbytes = pwrite(fd, buf, len, offset);
    if (seekable && nbytes > 0) {
        r = sys_lseek(fd, offset + nbytes);
        assert(r == 0, "sys_lseek");
    }
    return nbytes;
}

int unlinkat(int dirfd, const char *pathname, int flags)
{
    int r;

    ping->unlink.dirfd = cwd_fd;
    strcpy(ping->unlink.path, pathname);
    ping->unlink.flags = flags;
    r = sys_call(FSPID, FSIPC_UNLINK, virt_to_pn(ping), sizeof(ping->unlink), virt_to_pn(pong), -1);
    assert(r == 0, "sys_call");
    r = (int)ucurrent->ipc_val;
    return r;
}

int unlink(const char *pathname)
{
    return unlinkat(cwd_fd, pathname, 0);
}

struct file *fd_to_file(int fd)
{
    fn_t fn;

    assert(is_fd_valid(fd), "fd must be valid");
    fn = ucurrent->ofile[fd];
    assert(is_fn_valid(fn), "fn must be valid");
    return &ufiles[fn];
}
