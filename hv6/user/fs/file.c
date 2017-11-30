#include "fs.h"

static struct inode *create(struct file *cwd, char *path, short type, short major, short minor)
{
    uint off;
    struct inode *ip, *dp;
    char name[DIRSIZ];

    if ((dp = nameiparent(cwd, path, name)) == 0)
        return 0;

    ilock(dp);

    if ((ip = dirlookup(dp, name, &off)) != 0) {
        iunlockput(dp);
        ilock(ip);
        if (type == T_FILE && ip->type == T_FILE)
            return ip;
        iunlockput(ip);
        return 0;
    }

    if ((ip = ialloc(dp->dev, type)) == 0)
        panic("create: ialloc");

    ilock(ip);
    ip->major = major;
    ip->minor = minor;
    ip->nlink = 1;
    ip->atime = ip->mtime = ip->ctime = unix_time();
    iupdate(ip);

    /* create . and .. entries */
    if (type == T_DIR) {
        /* for ".." */
        dp->nlink++;
        iupdate(dp);
        /* no ip->nlink++ for ".": avoid cyclic ref count */
        if (dirlink(ip, ".", ip->inum) < 0 || dirlink(ip, "..", dp->inum) < 0)
            panic("create dots");
    }

    if (dirlink(dp, name, ip->inum) < 0)
        panic("create: dirlink");

    iunlockput(dp);

    return ip;
}

int fileopen(struct file *cwd, char *path, int omode)
{
    struct inode *ip;
    int fd, r;

    begin_op();

    if (omode & O_CREAT) {
        ip = create(cwd, path, T_FILE, 0, 0);
        if (ip == 0) {
            end_op();
            return -EIO;
        }
    } else {
        if ((ip = namei(cwd, path)) == 0) {
            end_op();
            return -EIO;
        }
        ilock(ip);
        if (ip->type == T_DIR && omode != O_RDONLY) {
            iunlockput(ip);
            end_op();
            return -EIO;
        }
    }

    iunlock(ip);
    end_op();

    fd = find_lowest_free_fd();
    r = sys_create(fd, find_free_fn(), FD_INODE, (uintptr_t)ip, omode);
    assert(r == 0, "sys_create");
    return fd;
}

int filepread(struct file *f, char *addr, size_t count, size_t offset)
{
    int r;

    if (file_readable(f) == 0)
        return -EACCES;
    if (f->type == FD_PIPE)
        return piperead(file_pipe(f), addr, count);
    if (f->type == FD_INODE) {
        ilock(file_ip(f));
        r = readi(file_ip(f), addr, offset, count);
        iunlock(file_ip(f));
        return r;
    }
    panic("fileread");
}

int filemknod(struct file *cwd, char *path, short major, short minor)
{
    struct inode *ip;

    begin_op();
    if ((ip = create(cwd, path, T_DEV, major, minor)) == 0) {
        end_op();
        return -1;
    }
    iunlockput(ip);
    end_op();
    return 0;
}

int filemkdir(struct file *cwd, char *path)
{
    struct inode *ip;

    begin_op();
    if ((ip = create(cwd, path, T_DIR, 0, 0)) == 0) {
        end_op();
        return -1;
    }
    iunlockput(ip);
    end_op();
    return 0;
}

/* is the directory dp empty except for "." and ".." */
static int isdirempty(struct inode *dp)
{
    int off;
    struct dirent de;

    for (off = 2 * sizeof(de); off < dp->size; off += sizeof(de)) {
        if (readi(dp, (char *)&de, off, sizeof(de)) != sizeof(de))
            panic("isdirempty: readi");
        if (de.inum != 0)
            return 0;
    }
    return 1;
}

int fileunlink(struct file *cwd, char *path)
{
    struct inode *ip, *dp;
    struct dirent de;
    char name[DIRSIZ];
    uint off;
    int r = -EINVAL;

    begin_op();

    if ((dp = nameiparent(cwd, path, name)) == 0)
        goto bad;

    ilock(dp);

    /* cannot unlink "." or ".." */
    if (namecmp(name, ".") == 0 || namecmp(name, "..") == 0)
        goto bad;

    if ((ip = dirlookup(dp, name, &off)) == 0) {
        r = -ENOENT;
        goto bad;
    }

    ilock(ip);

    if (ip->nlink < 1)
        panic("unlink: nlink < 1");

    if (ip->type == T_DIR && !isdirempty(ip)) {
        iunlockput(ip);
        goto bad;
    }

    memset(&de, 0, sizeof(de));
    if (writei(dp, (char *)&de, off, sizeof(de)) != sizeof(de))
        panic("unlink: writei");
    if (ip->type == T_DIR) {
        dp->nlink--;
        iupdate(dp);
    }
    iunlockput(dp);
    ip->nlink--;
    iupdate(ip);
    iunlockput(ip);

    end_op();
    return 0;

bad:
    iunlockput(dp);
    end_op();
    return r;
}

// Get metadata about file f.
int filestat(struct file *f, struct stat *st)
{
    if (f->type == FD_INODE) {
        ilock(file_ip(f));
        stati(file_ip(f), st);
        iunlock(file_ip(f));
        return 0;
    }
    return -1;
}

int filepwrite(struct file *f, char *addr, size_t n, size_t offset)
{
    int r;

    if (file_writable(f) == 0) {
        cprintf("not writeable\n");
        return -1;
    }
    if (f->type == FD_PIPE)
        return pipewrite(file_pipe(f), addr, n);
    if (f->type == FD_INODE) {
        // write a few blocks at a time to avoid exceeding
        // the maximum log transaction size, including
        // i-node, indirect block, allocation blocks,
        // and 2 blocks of slop for non-aligned writes.
        // this really belongs lower down, since writei()
        // might be writing a device like the console.
        int max = ((LOGSIZE - 1 - 1 - 2) / 2) * 512;

        if (offset > file_ip(f)->size) { // fill in hole
            // XXX break up writing hole if off- ip->size > max
            int n = offset - file_ip(f)->size;
            begin_op();
            ilock(file_ip(f));
            zeroi(file_ip(f), file_ip(f)->size, n);
            iunlock(file_ip(f));
            end_op();
        }
        int i = 0;
        while (i < n) {
            int n1 = n - i;
            if (n1 > max)
                n1 = max;

            begin_op();
            ilock(file_ip(f));
            if ((r = writei(file_ip(f), addr + i, offset, n1)) > 0)
                offset += r;
            iunlock(file_ip(f));
            end_op();

            if (r < 0)
                break;
            if (r != n1)
                panic("short filewrite");
            i += r;
        }
        return i == n ? n : -1;
    }
    panic("filewrite");
}
