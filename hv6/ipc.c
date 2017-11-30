#include <string.h>
#include "ipc.h"
#include "proc.h"

int send_proc(pid_t pid, uint64_t val, pn_t pn, size_t size, int fd)
{
    struct proc *sender, *receiver;

    if (!is_pid_valid(pid))
        return -ESRCH;
    if (!is_proc_state(pid, PROC_SLEEPING))
        return -EAGAIN;
    if (!is_pn_valid(pn))
        return -EINVAL;
    /* pn doesn't have to be a frame */
    if (!is_page_pid(pn, current))
        return -EACCES;
    if (size > PAGE_SIZE)
        return -EINVAL;
    if (is_fd_valid(fd)) {
        if (!is_fn_valid(get_fd(current, fd)))
            return -EINVAL;
    }

    assert(pid != current, "current is running and pid is sleeping");

    sender = get_proc(current);
    receiver = get_proc(pid);

    receiver->ipc_from = current;
    receiver->ipc_val = val;
    receiver->ipc_size = size;
    /* invariant: proc->ipc_page is a valid page owned by pid */
    memcpy(get_page(receiver->ipc_page), get_page(pn), size);
    /* invariant: ipc_fd is empty if it's valid */
    if (is_fd_valid(fd) && is_fd_valid(receiver->ipc_fd))
        set_fd(pid, receiver->ipc_fd, get_fd(current, fd));

    sender->state = PROC_RUNNABLE;
    receiver->state = PROC_RUNNING;
    /* receiver: sleeping -> running */
    proc_ready_add(receiver);
    current = pid;
    return 0;
}

/*
 * This is called by sys_recv in entry.S.
 * - Upon entry, current's hvm is already flushed.
 * - Upon exit, run_current() is called to return to user space.
 */
int recv_proc(pid_t pid, pn_t pn, int fd)
{
    struct proc *server;

    if (!is_pid_valid(pid))
        return -ESRCH;
    if (!is_proc_state(pid, PROC_RUNNABLE))
        return -EINVAL;
    if (!is_pn_valid(pn))
        return -EINVAL;
    if (!is_page_pid(pn, current))
        return -EACCES;
    if (!is_page_type(pn, PAGE_TYPE_FRAME))
        return -EINVAL;
    if (is_fd_valid(fd)) {
        if (is_fn_valid(get_fd(current, fd)))
            return -EINVAL;
    }

    assert(pid != current, "current is running and pid is runnable");
    server = get_proc(current);
    server->ipc_from = 0;
    server->ipc_page = pn;
    server->ipc_size = 0;
    server->ipc_fd = fd;

    server->state = PROC_SLEEPING;
    /* server: running -> sleeping */
    proc_ready_del(server);
    get_proc(pid)->state = PROC_RUNNING;
    current = pid;
    return 0;
}

static int send_recv(pid_t pid, uint64_t val, pn_t inpn, size_t size, int infd, pn_t outpn,
                     int outfd)
{
    struct proc *sender, *receiver;

    /* target process must be sleeping */
    if (!is_pid_valid(pid))
        return -ESRCH;
    if (!is_proc_state(pid, PROC_SLEEPING))
        return -EAGAIN;
    /* check in page */
    if (!is_pn_valid(inpn))
        return -EINVAL;
    /* inpn doesn't have to be a frame */
    if (!is_page_pid(inpn, current))
        return -EACCES;
    if (size > PAGE_SIZE)
        return -EINVAL;
    /* check in fd: either invalid or non-empty */
    if (is_fd_valid(infd)) {
        if (!is_fn_valid(get_fd(current, infd)))
            return -EINVAL;
    }
    /* check out page */
    if (!is_pn_valid(outpn))
        return -EINVAL;
    if (!is_page_pid(outpn, current))
        return -EACCES;
    if (!is_page_type(outpn, PAGE_TYPE_FRAME))
        return -EINVAL;
    /* check out fd: either invalid or empty */
    if (is_fd_valid(outfd)) {
        if (is_fn_valid(get_fd(current, outfd)))
            return -EINVAL;
    }

    assert(pid != current, "current is running and pid is sleeping");

    sender = get_proc(current);
    receiver = get_proc(pid);

    /* check if the receiver wants to accept anyone's request */
    if (receiver->ipc_from && receiver->ipc_from != current)
        return -EACCES;

    /* client: prepare for response */
    sender->ipc_page = outpn;
    sender->ipc_fd = outfd;

    /* server: transfer data from client */
    receiver->ipc_from = current;
    receiver->ipc_val = val;
    /* transfer the page */
    memcpy(get_page(receiver->ipc_page), get_page(inpn), size);
    receiver->ipc_size = size;
    /* transfer the fd */
    if (is_fd_valid(infd) && is_fd_valid(receiver->ipc_fd))
        set_fd(pid, receiver->ipc_fd, get_fd(current, infd));

    /* switch control */

    sender->state = PROC_SLEEPING;
    receiver->state = PROC_RUNNING;
    /* receiver: sleeping -> running */
    proc_ready_add(receiver);
    /* sender: running -> sleeping */
    proc_ready_del(sender);
    return 0;
}

int reply_wait_proc(pid_t pid, uint64_t val, pn_t inpn, size_t size, int infd, pn_t outpn)
{
    int r;

    r = send_recv(pid, val, inpn, size, infd, outpn, -1);
    if (r)
        return r;
    /* accept any ipc */
    get_proc(current)->ipc_from = 0;
    current = pid;
    return 0;
}

int call_proc(pid_t pid, uint64_t val, pn_t inpn, size_t size, pn_t outpn, int outfd)
{
    int r;

    r = send_recv(pid, val, inpn, size, -1, outpn, outfd);
    if (r)
        return r;
    /* accept any ipc */
    get_proc(current)->ipc_from = pid;
    current = pid;
    return 0;
}
