#include "fs.h"

#define PIPESIZE 512

struct pipe {
    struct spinlock lock;
    char data[PIPESIZE];
    uint nread;    /* number of bytes read */
    uint nwrite;   /* number of bytes written */
    int readopen;  /* read fd is still open */
    int writeopen; /* write fd is still open */
};

int pipealloc(int fds[2])
{
    struct pipe *p;
    int fd0, fd1, r;

    p = malloc(sizeof(struct pipe));
    assert(p, "malloc");
    p->readopen = 1;
    p->writeopen = 1;
    p->nwrite = 0;
    p->nread = 0;

    fd0 = find_lowest_free_fd();
    fd1 = find_free_fd(fd0 + 1);
    r = sys_create(fd0, find_free_fn(), FD_PIPE, (uintptr_t)p, O_RDONLY);
    assert(r == 0, "sys_create");
    r = sys_create(fd1, find_free_fn(), FD_PIPE, (uintptr_t)p, O_WRONLY);
    assert(r == 0, "sys_create");
    fds[0] = fd0;
    fds[1] = fd1;
    return 0;
}

void pipeclose(struct pipe *p, int writable)
{
    acquire(&p->lock);
    if (writable) {
        p->writeopen = 0;
        wakeup(&p->nread);
    } else {
        p->readopen = 0;
        wakeup(&p->nwrite);
    }
    if (p->readopen == 0 && p->writeopen == 0) {
        release(&p->lock);
        free((char *)p);
    } else
        release(&p->lock);
}

int pipewrite(struct pipe *p, char *addr, int n)
{
    int i;

    acquire(&p->lock);
    for (i = 0; i < n; i++) {
        /* pipewrite-full */
        if (p->nwrite == p->nread + PIPESIZE) {
            if (p->readopen == 0) {
                release(&p->lock);
                return -EPIPE;
            }
            release(&p->lock);
            return i ? i : -EAGAIN;
        }
        p->data[p->nwrite++ % PIPESIZE] = addr[i];
    }
    release(&p->lock);
    return n;
}

int piperead(struct pipe *p, char *addr, int n)
{
    int i;

    acquire(&p->lock);
    /* pipe-empty */
    if (p->nread == p->nwrite && p->writeopen) {
        release(&p->lock);
        return -EAGAIN;
    }
    for (i = 0; i < n; i++) {
        if (p->nread == p->nwrite)
            break;
        addr[i] = p->data[p->nread++ % PIPESIZE];
    }
    release(&p->lock);
    return i;
}
