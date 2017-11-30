#include <lwip/arch.h>
#include <lwip/ip_addr.h>
#include "ns.h"
#include "socket.h"

static uint8_t ping_buf[PAGE_SIZE] __aligned(PAGE_SIZE);
static uint8_t pong_buf[PAGE_SIZE] __aligned(PAGE_SIZE);
static struct nsipc_ping *ping = (void *)ping_buf;
static struct nsipc_pong *pong = (void *)pong_buf;

char *inet_ntoa(struct in_addr in)
{
    static char buf[16];

    return inet_ntoa_r(in, buf, sizeof(buf));
}

char *inet_ntoa_r(struct in_addr in, char *buf, size_t size)
{
    uint32_t s_addr;
    char inv[3];
    char *rp;
    uint8_t *ap;
    uint8_t rem;
    uint8_t n;
    uint8_t i;
    int len = 0;

    s_addr = in.s_addr;
    rp = buf;
    ap = (uint8_t *)&s_addr;
    for (n = 0; n < 4; n++) {
        i = 0;
        do {
            rem = *ap % (uint8_t)10;
            *ap /= (uint8_t)10;
            inv[i++] = (char)('0' + rem);
        } while (*ap);
        while (i--) {
            if (len++ >= size) {
                return NULL;
            }
            *rp++ = inv[i];
        }
        if (len++ >= size) {
            return NULL;
        }
        *rp++ = '.';
        ap++;
    }
    *--rp = 0;
    return buf;
}

struct hostent *gethostbyname(const char *name)
{
    static ip_addr_t addr;
    static void *addr_list[2] = {&addr, NULL};
    static struct hostent hostent = {.h_addr_list = (char **)addr_list};
    size_t len;
    int r;

    len = strlen(name) + 1;
    memcpy(ping, name, len);
    while (1) {
        r = sys_call(NSPID, NSIPC_GETHOSTBYNAME, virt_to_pn(ping), len, virt_to_pn(pong), -1);
        if (r == -EAGAIN) {
            yield();
            continue;
        }
        assert(r == 0, "sys_call");
        break;
    }
    if (ucurrent->ipc_val)
        return NULL;
    memcpy(&addr, pong, ucurrent->ipc_size);
    hostent.h_name = (char *)name;
    hostent.h_aliases = NULL;
    hostent.h_addrtype = AF_INET;
    hostent.h_length = ucurrent->ipc_size;
    return &hostent;
}

int socket(int domain, int type, int protocol)
{
    int fd, r;

    ping->socket.domain = domain;
    ping->socket.type = type;
    ping->socket.protocol = protocol;
    fd = find_lowest_free_fd();
    while (1) {
        r = sys_call(NSPID, NSIPC_SOCKET, virt_to_pn(ping), sizeof(ping->socket), virt_to_pn(pong),
                     fd);
        if (r == -EAGAIN) {
            yield();
            continue;
        }
        assert(r == 0, "sys_call");
        break;
    }
    r = (int)ucurrent->ipc_val;
    if (r < 0)
        return r;
    assert(fd_to_file(fd)->type == FD_SOCKET, "must be socket");
    return fd;
}

int getsockopt(int sockfd, int level, int optname, void *optval, socklen_t *optlen)
{
    int r;

    ping->getsockopt.sockfd = sockfd;
    ping->getsockopt.level = level;
    ping->getsockopt.optname = optname;
    while (1) {
        r = sys_call(NSPID, NSIPC_GETSOCKOPT, virt_to_pn(ping), sizeof(ping->getsockopt),
                     virt_to_pn(pong), -1);
        if (r == -EAGAIN) {
            yield();
            continue;
        }
        assert(r == 0, "sys_call");
        break;
    }
    r = ucurrent->ipc_val;
    *(int *)optval = r;
    *optlen = sizeof(int);
    return 0;
}

int connect(int sockfd, const struct sockaddr *addr, socklen_t addrlen)
{
    int r;

    ping->connect.sockfd = sockfd;
    ping->connect.addr = ((struct sockaddr_in *)addr)->sin_addr.s_addr;
    ping->connect.port = ntohs(((struct sockaddr_in *)addr)->sin_port);
    while (1) {
        r = sys_call(NSPID, NSIPC_CONNECT, virt_to_pn(ping), sizeof(ping->connect),
                     virt_to_pn(pong), -1);
        if (r == -EAGAIN) {
            yield();
            continue;
        }
        assert(r == 0, "sys_call");
        break;
    }
    r = (int)ucurrent->ipc_val;
    return r;
}

int bind(int sockfd, const struct sockaddr *addr, socklen_t addrlen)
{
    int r;

    ping->bind.sockfd = sockfd;
    ping->bind.addr = ((struct sockaddr_in *)addr)->sin_addr.s_addr;
    ping->bind.port = ntohs(((struct sockaddr_in *)addr)->sin_port);
    while (1) {
        r = sys_call(NSPID, NSIPC_BIND, virt_to_pn(ping), sizeof(ping->bind), virt_to_pn(pong), -1);
        if (r == -EAGAIN) {
            yield();
            continue;
        }
        assert(r == 0, "sys_call");
        break;
    }
    r = (int)ucurrent->ipc_val;
    return r;
}

int listen(int sockfd, int backlog)
{
    int fd, r;

    ping->listen.sockfd = sockfd;
    ping->listen.backlog = backlog;
    fd = find_lowest_free_fd();
    while (1) {
        r = sys_call(NSPID, NSIPC_LISTEN, virt_to_pn(ping), sizeof(ping->listen), virt_to_pn(pong),
                     fd);
        if (r == -EAGAIN) {
            yield();
            continue;
        }
        assert(r == 0, "sys_call");
        break;
    }
    r = (int)ucurrent->ipc_val;
    return r;
}

int accept(int sockfd, struct sockaddr *addr, socklen_t *addrlen)
{
    int fd, r;

    ping->accept.sockfd = sockfd;
    fd = find_lowest_free_fd();
    while (1) {
        r = sys_call(NSPID, NSIPC_ACCEPT, virt_to_pn(ping), sizeof(ping->accept), virt_to_pn(pong),
                     fd);
        if (r == -EAGAIN) {
            yield();
            continue;
        }
        assert(r == 0, "sys_call");
        r = (int)ucurrent->ipc_val;
        if (r == -EAGAIN) {
            yield();
            continue;
        }
        if (r < 0)
            return r;
        break;
    }
    assert(fd_to_file(fd)->type == FD_SOCKET, "must be socket");
    if (addr) {
        struct sockaddr_in *sockaddr = (void *)addr;

        memset(sockaddr, 0, sizeof(*sockaddr));
        sockaddr->sin_len = sizeof(*sockaddr);
        sockaddr->sin_family = PF_INET;
        sockaddr->sin_addr.s_addr = pong->accept.addr;
        sockaddr->sin_port = htons(pong->accept.port);
    }
    if (addrlen)
        *addrlen = sizeof(struct sockaddr_in);
    return fd;
}

ssize_t send(int sockfd, const void *buf, size_t len, int flags)
{
    ssize_t r;

    ping->send.sockfd = sockfd;
    ping->send.flags = flags;
    len = min(len, PAGE_SIZE - sizeof(ping->send));
    memcpy(ping->send.buf, buf, len);
    while (1) {
        r = sys_call(NSPID, NSIPC_SEND, virt_to_pn(ping), sizeof(ping->send) + len,
                     virt_to_pn(pong), -1);
        if (r == -EAGAIN) {
            yield();
            continue;
        }
        assert(r == 0, "sys_call");
        r = (ssize_t)ucurrent->ipc_val;
        if (r == -EAGAIN) {
            yield();
            continue;
        }
        break;
    }
    return r;
}

ssize_t recv(int sockfd, void *buf, size_t len, int flags)
{
    ssize_t r;

    ping->recv.sockfd = sockfd;
    ping->recv.len = len;
    ping->recv.flags = flags;
    while (1) {
        r = sys_call(NSPID, NSIPC_RECV, virt_to_pn(ping), sizeof(ping->recv), virt_to_pn(pong), -1);
        if (r == -EAGAIN) {
            yield();
            continue;
        }
        assert(r == 0, "sys_call");
        r = (ssize_t)ucurrent->ipc_val;
        if (r == -EAGAIN) {
            yield();
            continue;
        }
        if (r < 0)
            return r;
        break;
    }
    r = (ssize_t)ucurrent->ipc_size;
    assert(r <= len, "recv size");
    memcpy(buf, pong, r);
    return r;
}
