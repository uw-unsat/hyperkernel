#include "fd.h"
#include "proc.h"

struct file file_table[NFILE] __aligned(PAGE_SIZE);

static inline void clear_fd(pid_t pid, int fd)
{
    struct proc *proc;
    struct file *file;

    proc = get_proc(pid);
    file = get_file(get_fd(pid, fd));
    proc->ofile[fd] = 0;
    --proc->nr_fds;
    if (--file->refcnt == 0) {
        file->type = FD_NONE;
        file->value = 0;
        file->offset = 0;
        file->omode = 0;
    }
}

int sys_create(int fd, fn_t fn, uint64_t type, uint64_t value, uint64_t omode)
{
    struct file *file;

    if (type == FD_NONE)
        return -EINVAL;
    if (!is_fd_valid(fd))
        return -EBADF;
    /* fd must be empty */
    if (get_fd(current, fd) != 0)
        return -EINVAL;
    if (!is_fn_valid(fn))
        return -EINVAL;
    /* fn must be unused */
    file = get_file(fn);
    if (file->refcnt != 0)
        return -EINVAL;

    file->type = type;
    file->value = value;
    file->omode = omode;
    file->refcnt = 0;
    file->offset = 0;
    set_fd(current, fd, fn);
    return 0;
}

int sys_close(pid_t pid, int fd)
{
    if (!is_pid_valid(pid))
        return -ESRCH;
    if (!is_fd_valid(fd))
        return -EBADF;
    /* permission check: current or a dead pid */
    if (pid != current && !is_proc_state(pid, PROC_ZOMBIE))
        return -EACCES;
    if (get_fd(pid, fd) == 0)
        return -EBADF;
    clear_fd(pid, fd);
    return 0;
}

int sys_dup(int oldfd, pid_t pid, int newfd)
{
    fn_t fn;

    if (!is_pid_valid(pid))
        return -ESRCH;
    if (!is_current_or_embryo(pid))
        return -EACCES;
    /* oldfd doesn't exist  */
    if (!is_fd_valid(oldfd))
        return -EBADF;
    fn = get_fd(current, oldfd);
    if (fn == 0)
        return -EBADF;
    if (!is_fd_valid(newfd))
        return -EBADF;
    /* newfd already exists */
    if (get_fd(pid, newfd) != 0)
        return -EINVAL;

    set_fd(pid, newfd, fn);
    return 0;
}

int sys_dup2(int oldfd, pid_t pid, int newfd)
{
    fn_t fn;

    if (!is_pid_valid(pid))
        return -ESRCH;
    if (!is_current_or_embryo(pid))
        return -EACCES;
    /* oldfd doesn't exist  */
    if (!is_fd_valid(oldfd))
        return -EBADF;
    fn = get_fd(current, oldfd);
    if (fn == 0)
        return -EBADF;
    if (!is_fd_valid(newfd))
        return -EBADF;

    /* POSIX: do nothing for the same fd */
    if ((current == pid) && (oldfd == newfd))
        return 0;

    /* close newfd if it already exists */
    if (get_fd(pid, newfd) != 0)
        clear_fd(pid, newfd);
    set_fd(pid, newfd, fn);
    return 0;
}

int sys_lseek(int fd, off_t offset)
{
    fn_t fn;
    struct file *file;

    if (!is_fd_valid(fd))
        return -EBADF;
    fn = get_fd(current, fd);
    if (!is_file_type(fn, FD_INODE))
        return -EINVAL;
    if (offset < 0)
        return -EINVAL;
    file = get_file(fn);

    file->offset = offset;
    return 0;
}
