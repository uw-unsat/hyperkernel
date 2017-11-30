#include <lwip/dhcp.h>
#include <lwip/dns.h>
#include <lwip/etharp.h>
#include <lwip/inet.h>
#include <lwip/init.h>
#include <lwip/netif.h>
#include <lwip/prot/dhcp.h>
#include <lwip/tcp.h>
#include <lwip/timeouts.h>
#include <lwip/udp.h>
#include <uapi/e1000.h>
#include <uapi/pcidb.h>
#include <uapi/pcireg.h>
#include "ns.h"
#include "uiommu.h"

#define TRAP_USER 250

#define DATA_MAX 1518
#define TX_RING_SIZE 64
#define RX_RING_SIZE 64

struct eerd {
    uint32_t data_shift;
    uint32_t addr_shift;
    uint32_t done_bit;
    uint32_t start_bit;
};

static const struct eerd *eerd;

static size_t pci_index = -1;

/* iommu_map() asks data structures to take entire pages */

static struct {
    struct e1000_tx_desc ring[TX_RING_SIZE];
    char data[TX_RING_SIZE][DATA_MAX];
    uint8_t padding[ALIGN(TX_RING_SIZE * (sizeof(struct e1000_tx_desc) + DATA_MAX), PAGE_SIZE)];
} __packed __aligned(PAGE_SIZE) tx;

static struct {
    struct e1000_rx_desc ring[RX_RING_SIZE] __aligned(PAGE_SIZE);
    char data[RX_RING_SIZE][2048] __aligned(PAGE_SIZE);
    uint8_t padding[ALIGN(RX_RING_SIZE * (sizeof(struct e1000_rx_desc) + 2048), PAGE_SIZE)];
} __packed __aligned(PAGE_SIZE) rx;

static uint8_t mac[6];
static void *regs;

static uint8_t ping_buf[PAGE_SIZE] __aligned(PAGE_SIZE);
static uint8_t pong_buf[PAGE_SIZE] __aligned(PAGE_SIZE);
static struct nsipc_ping *ping = (void *)ping_buf;
static struct nsipc_pong *pong = (void *)pong_buf;

typedef int (*handler_t)(pid_t);

static int do_timer(pid_t);
static int do_gethostbyname(pid_t);
static int do_socket(pid_t);
static int do_getsockopt(pid_t);
static int do_connect(pid_t);
static int do_bind(pid_t);
static int do_listen(pid_t);
static int do_accept(pid_t);
static int do_send(pid_t);
static int do_recv(pid_t);

static handler_t handlers[] = {
        [NSIPC_TIMER] = do_timer,     [NSIPC_GETHOSTBYNAME] = do_gethostbyname,
        [NSIPC_SOCKET] = do_socket,   [NSIPC_GETSOCKOPT] = do_getsockopt,
        [NSIPC_CONNECT] = do_connect, [NSIPC_BIND] = do_bind,
        [NSIPC_LISTEN] = do_listen,   [NSIPC_ACCEPT] = do_accept,
        [NSIPC_SEND] = do_send,       [NSIPC_RECV] = do_recv,
};

static void init_timer(void);
static void init_pci(void);
static void reset(void);
static void init_link(void);
static void init_tx(void);
static void init_rx(void);
static void init_irq(void);
static void init_netif(struct netif *);
static void gc(void);
static void irq_handler(void);

static void eeprom_read(uint16_t *buf, size_t off, size_t len);
static int e1000_transmit(const char *buf, size_t len);
static int e1000_receive(char *buf, size_t len);

static struct netif e1000_netif;

struct socket {
    int fd;
    void *pcb;
    pid_t pid;
    struct pbuf *recv_buf;
    int recv_offset;
    int recv_closed;
    struct socket *backlog[5];
    int protocol;
};

static struct socket *fd_lookup(pid_t pid, int fd);

int main(int argc, char **argv)
{
    int r;

    init_timer();
    init_pci();
    reset();
    init_link();
    init_rx();
    init_tx();
    init_irq();
    init_netif(&e1000_netif);

    r = sys_recv(INITPID, virt_to_pn(ping), -1);
    while (1) {
        if (r == 0) {
            pid_t pid = ucurrent->ipc_from;
            size_t op = ucurrent->ipc_val;

            if (bit_isset(TRAP_USER, ucurrent->intr)) {
                irq_handler();
                sys_ack_intr(TRAP_USER);
            }
            if (is_pid_valid(pid) && op < countof(handlers)) {
                handler_t handler;

                handler = handlers[op];
                if (handler) {
                    gc();
                    r = handler(pid);
                    continue;
                }
            }
        }
        r = sys_recv(INITPID, virt_to_pn(ping), -1);
    }
    exit();
}

static int do_timer(pid_t pid)
{
    static char buf[DATA_MAX];
    size_t n;
    struct netif *netif = &e1000_netif;

    n = e1000_receive(buf, sizeof(buf));
    if (n) {
        struct pbuf *p, *q;
        size_t copied = 0;

        p = pbuf_alloc(PBUF_RAW, sizeof(buf), PBUF_POOL);
        for (q = p; q != NULL; q = q->next) {
            size_t len = min((size_t)q->len, n - copied);

            memcpy(q->payload, buf + copied, len);
            copied += len;
        }

        if (netif->input(p, netif) != ERR_OK) {
            cprintf("ns: drop packet (%zu bytes)\n", n);
            pbuf_free(p);
        }
    }

    /* lwIP timers check */
    sys_check_timeouts();

    /* no reply for timer */
    return -1;
}

/* callback from dns_gethostbyname */
static void dns_found(const char *name, const ip_addr_t *ipaddr, void *arg)
{
    pid_t pid = (pid_t)(intptr_t)arg;
    int r;

    if (ipaddr) {
        memcpy(pong, ipaddr, sizeof(ip_addr_t));
        r = sys_send(pid, 0, virt_to_pn(pong), sizeof(ip_addr_t), -1);
    } else {
        r = sys_send(pid, -EHOSTUNREACH, virt_to_pn(pong), 0, -1);
    }
    assert(r == 0, "sys_send");
}

static int do_gethostbyname(pid_t pid)
{
    int r;

    r = dns_gethostbyname((void *)ping, (void *)pong, dns_found, (void *)(intptr_t)pid);
    switch (r) {
    default:
        break;
    case ERR_OK:
        return sys_reply_wait(pid, 0, virt_to_pn(pong), sizeof(ip_addr_t), -1, virt_to_pn(ping));
    case ERR_INPROGRESS:
        /* will reply in dns_found */
        return -1;
    }
    return sys_reply_wait(pid, -EINVAL, virt_to_pn(pong), 0, -1, virt_to_pn(ping));
}

static void free_socket(struct socket *socket)
{
    size_t i, n = countof(socket->backlog);
    pid_t pid = socket->pid;
    int r;

    close(socket->fd);
    if (socket->recv_buf)
        pbuf_free(socket->recv_buf);

    if (socket->pcb) {
        switch (socket->protocol) {
        default:
            assert(false, "unknown protocol");
        case IPPROTO_TCP:
            tcp_close(socket->pcb);
            break;
        case IPPROTO_UDP:
            udp_remove(socket->pcb);
            break;
        }
        /* free pcb */
        tcp_close(socket->pcb);
        socket->pcb = NULL;
    }

    /* clean up pending socket */
    for (i = 0; i < n; ++i) {
        struct socket *pending = socket->backlog[i];

        if (pending)
            free_socket(pending);
    }

    memset(socket, 0, sizeof(struct socket));
    free(socket);

    /* just in case if client is still waiting */
    if (is_pid_valid(pid) && uprocs[pid].state == PROC_SLEEPING &&
        uprocs[pid].ipc_from == getpid()) {
        socket->pid = 0;
        r = sys_send(pid, -ECONNRESET, virt_to_pn(pong), 0, -1);
        assert(r == 0, "sys_send");
    }
}

err_t lwip_tcp_event(void *arg, struct tcp_pcb *pcb, enum lwip_event event, struct pbuf *p,
                     u16_t size, err_t err)
{
    struct socket *socket = arg;
    pid_t pid = socket->pid;
    int r;

    switch (event) {
    case LWIP_EVENT_ACCEPT:
        if (err == ERR_OK) {
            size_t i, n = countof(socket->backlog);
            struct socket *newsocket;

            for (i = 0; i < n; ++i) {
                if (!socket->backlog[i])
                    break;
            }
            /* queue full */
            if (i == n)
                return ERR_MEM;
            assert(pcb->listener == socket->pcb, "listener/arg must match");
            newsocket = malloc(sizeof(struct socket));
            memset(newsocket, 0, sizeof(struct socket));
            /* the passed in pcb is for the new socket */
            newsocket->pcb = pcb;
            tcp_arg(pcb, newsocket);
            newsocket->protocol = socket->protocol;
            socket->backlog[i] = newsocket;
        }
        return ERR_OK;
    case LWIP_EVENT_SENT:
        /* ignore */
        return ERR_OK;
    case LWIP_EVENT_RECV:
        /* closed or error */
        if (!p || err != ERR_OK) {
            if (p)
                pbuf_free(p);
            socket->recv_closed = 1;
            return ERR_OK;
        }
        /* buffer hasn't been received */
        if (socket->recv_buf)
            return ERR_MEM;
        /* ack the packet */
        tcp_recved(socket->pcb, p->tot_len);
        socket->recv_buf = p;
        socket->recv_offset = 0;
        return ERR_OK;
    case LWIP_EVENT_CONNECTED:
        assert(is_pid_valid(pid), "connect must have been called");
        /* reset */
        socket->pid = 0;
        /* reply */
        r = (err == ERR_OK) ? 0 : -ECONNRESET;
        r = sys_send(pid, r, virt_to_pn(pong), 0, -1);
        assert(r == 0, "sys_send");
        return ERR_OK;
    case LWIP_EVENT_POLL:
        /* ignore */
        return ERR_OK;
    case LWIP_EVENT_ERR:
        /* pcb is already deallocated */
        socket->pcb = NULL;
        /* let gc do the job: free_socket(socket); */
        return ERR_ABRT;
    default:
        break;
    }

    assert(false, "unreachable");
}

static int do_socket(pid_t pid)
{
    struct socket *socket;
    void *pcb;
    int fd, r;

    assert(ucurrent->ipc_size == sizeof(ping->socket), "socket request size");
    assert(ping->socket.domain == PF_INET, "socket domain");

    fd = find_lowest_free_fd();
    socket = malloc(sizeof(struct socket));
    memset(socket, 0, sizeof(struct socket));
    socket->fd = fd;
    switch (ping->socket.protocol) {
    case IPPROTO_TCP:
        assert(ping->socket.type == SOCK_STREAM, "tcp socket type");
        pcb = tcp_new();
        tcp_arg(pcb, socket);
        break;
    case IPPROTO_UDP:
        assert(ping->socket.type == SOCK_DGRAM, "udp socket type");
        pcb = udp_new();
        break;
    default:
        free(socket);
        return sys_reply_wait(pid, -EPROTONOSUPPORT, virt_to_pn(pong), 0, -1, virt_to_pn(ping));
    }

    socket->protocol = ping->socket.protocol;
    socket->pcb = pcb;
    r = sys_create(fd, find_free_fn(), FD_SOCKET, (uintptr_t)socket, O_RDWR);
    assert(r == 0, "sys_create");
    return sys_reply_wait(pid, 0, virt_to_pn(pong), 0, fd, virt_to_pn(ping));
}

static int do_getsockopt(pid_t pid)
{
    struct socket *socket;
    int r = -EINVAL;

    socket = fd_lookup(pid, ping->getsockopt.sockfd);
    if (!socket)
        return sys_reply_wait(pid, -EBADF, virt_to_pn(pong), 0, -1, virt_to_pn(ping));

    assert(ping->getsockopt.level == SOL_SOCKET, "SOL_SOCKET only");
    switch (socket->protocol) {
    case IPPROTO_TCP:
        switch (ping->getsockopt.optname) {
        case SO_TYPE:
            r = SOCK_STREAM;
            break;
        default:
            break;
        }
        break;
    case IPPROTO_UDP:
        switch (ping->getsockopt.optname) {
        case SO_TYPE:
            r = SOCK_DGRAM;
            break;
        default:
            break;
        }
        break;
    default:
        r = -EBADF;
        break;
    }

    return sys_reply_wait(pid, r, virt_to_pn(pong), 0, -1, virt_to_pn(ping));
}

static int do_connect(pid_t pid)
{
    struct socket *socket;
    int r;

    socket = fd_lookup(pid, ping->connect.sockfd);
    if (!socket)
        return sys_reply_wait(pid, -EBADF, virt_to_pn(pong), 0, -1, virt_to_pn(ping));

    assert(!is_pid_valid(socket->pid), "socket already waited");
    switch (socket->protocol) {
    case IPPROTO_TCP:
        r = tcp_connect(socket->pcb, (ip_addr_t *)&ping->connect.addr, ping->connect.port, NULL);
        switch (r) {
        default:
            r = -EINVAL;
            break;
        case ERR_OK:
            /* reply in callback */
            socket->pid = pid;
            return -1;
        }
        break;
    case IPPROTO_UDP:
        assert(false, "TBD");
        break;
    default:
        r = -EBADF;
        break;
    }

    return sys_reply_wait(pid, r, virt_to_pn(pong), 0, -1, virt_to_pn(ping));
}

static int do_bind(pid_t pid)
{
    struct socket *socket;
    int r;

    socket = fd_lookup(pid, ping->bind.sockfd);
    if (!socket)
        return sys_reply_wait(pid, -EBADF, virt_to_pn(pong), 0, -1, virt_to_pn(ping));

    r = tcp_bind(socket->pcb, (ip_addr_t *)&ping->bind.addr, ping->bind.port);
    switch (r) {
    default:
        r = -EINVAL;
        break;
    case ERR_USE:
        r = -EADDRINUSE;
        break;
    case ERR_OK:
        r = 0;
        break;
    }
    return sys_reply_wait(pid, r, virt_to_pn(pong), 0, -1, virt_to_pn(ping));
}

static int do_listen(pid_t pid)
{
    struct socket *socket;
    void *newpcb;
    int r;

    socket = fd_lookup(pid, ping->listen.sockfd);
    if (!socket)
        return sys_reply_wait(pid, -EBADF, virt_to_pn(pong), 0, -1, virt_to_pn(ping));

    newpcb = tcp_listen_with_backlog(socket->pcb, ping->listen.backlog);
    if (newpcb) {
        r = 0;
        /* lwIP switches to a different pcb upon listen */
        socket->pcb = newpcb;
    } else {
        r = -ENOMEM;
    }

    return sys_reply_wait(pid, r, virt_to_pn(pong), 0, -1, virt_to_pn(ping));
}

static int do_accept(pid_t pid)
{
    struct socket *socket, *newsocket;
    size_t i, n = countof(socket->backlog);
    struct tcp_pcb *newpcb;
    int fd, r;

    socket = fd_lookup(pid, ping->accept.sockfd);
    if (!socket)
        return sys_reply_wait(pid, -EBADF, virt_to_pn(pong), 0, -1, virt_to_pn(ping));

    for (i = 0; i < n; ++i) {
        if (socket->backlog[i])
            break;
    }
    /* no accepted connection */
    if (i == n)
        return sys_reply_wait(pid, -EAGAIN, virt_to_pn(pong), 0, -1, virt_to_pn(ping));

    fd = find_lowest_free_fd();
    newsocket = socket->backlog[i];
    newsocket->fd = fd;
    socket->backlog[i] = NULL;

    r = sys_create(fd, find_free_fn(), FD_SOCKET, (uintptr_t)newsocket, O_RDWR);
    assert(r == 0, "sys_create");
    newpcb = newsocket->pcb;
    pong->accept.addr = newpcb->remote_ip.addr;
    pong->accept.port = newpcb->remote_port;
    return sys_reply_wait(pid, r, virt_to_pn(pong), sizeof(pong->accept), fd, virt_to_pn(ping));
}

static int do_send(pid_t pid)
{
    struct socket *socket;
    struct tcp_pcb *pcb;
    size_t len;
    int r;

    if (ucurrent->ipc_size <= sizeof(ping->send))
        return sys_reply_wait(pid, -EINVAL, virt_to_pn(pong), 0, -1, virt_to_pn(ping));
    socket = fd_lookup(pid, ping->send.sockfd);
    if (!socket)
        return sys_reply_wait(pid, -EBADF, virt_to_pn(pong), 0, -1, virt_to_pn(ping));

    pcb = socket->pcb;
    /* already closed */
    if (!pcb)
        return sys_reply_wait(pid, -ECONNRESET, virt_to_pn(pong), 0, -1, virt_to_pn(ping));

    /* send buffer full */
    if (!pcb->snd_buf)
        return sys_reply_wait(pid, -EAGAIN, virt_to_pn(pong), 0, -1, virt_to_pn(ping));

    len = ucurrent->ipc_size - sizeof(ping->send);
    /* limit to send buffer size */
    len = min(len, (size_t)pcb->snd_buf);
    r = tcp_write(pcb, ping->send.buf, len, TCP_WRITE_FLAG_COPY);
    switch (r) {
    default:
        r = -ECONNABORTED;
        break;
    case ERR_MEM:
        r = -EAGAIN;
        break;
    case ERR_OK:
        /* please send now */
        tcp_output(pcb);
        r = len;
        break;
    }
    return sys_reply_wait(pid, r, virt_to_pn(pong), 0, -1, virt_to_pn(ping));
}

static int do_recv(pid_t pid)
{
    struct socket *socket;
    int r;
    size_t len;

    if (ping->recv.len <= 0)
        return sys_reply_wait(pid, -EINVAL, virt_to_pn(pong), 0, -1, virt_to_pn(ping));

    socket = fd_lookup(pid, ping->recv.sockfd);
    if (!socket)
        return sys_reply_wait(pid, -EBADF, virt_to_pn(pong), 0, -1, virt_to_pn(ping));

    /* recv_buf is empty */
    if (!socket->recv_buf) {
        r = socket->recv_closed ? -ECONNRESET : -EAGAIN;
        return sys_reply_wait(pid, r, virt_to_pn(pong), 0, -1, virt_to_pn(ping));
    }

    /* recv_buf has data right now */
    len = pbuf_copy_partial(socket->recv_buf, pong, ping->recv.len, socket->recv_offset);
    socket->recv_offset += len;
    assert(socket->recv_offset <= socket->recv_buf->tot_len, "recv_offset");
    /* free pbuf */
    if (socket->recv_offset == socket->recv_buf->tot_len) {
        pbuf_free(socket->recv_buf);
        socket->recv_offset = 0;
        socket->recv_buf = NULL;
    }
    r = sys_reply_wait(pid, 0, virt_to_pn(pong), len, -1, virt_to_pn(ping));
    return r;
}

static void gc(void)
{
    int fd;
    fn_t fn;
    struct file *f;

    for (fd = 0; fd < NOFILE; ++fd) {
        fn = ucurrent->ofile[fd];
        struct socket *socket;

        if (!is_fn_valid(fn))
            continue;
        f = &ufiles[fn];
        if (f->refcnt != 1)
            continue;
        if (f->type != FD_SOCKET)
            continue;
        socket = (void *)(uintptr_t)f->value;
        free_socket(socket);
    }
}

static void e1000_write32(uint32_t index, uint32_t val)
{
    mmio_write32(regs + index, val);
}

static uint32_t e1000_read32(uint32_t index)
{
    return mmio_read32(regs + index);
}

static void e1000_flush(void)
{
    e1000_read32(E1000_STATUS);
}

static int e1000_transmit(const char *buf, size_t len)
{
    unsigned int tail;

    assert(len <= DATA_MAX, "len too large");

    tail = e1000_read32(E1000_TDT);
    assert(tail < RX_RING_SIZE, "invalid TX tail");
    /*
     * [E1000 3.3.3.2] Check if this descriptor is done.
     * According to [E1000 13.4.39], using TDH for this is not
     * reliable. */
    if (!(tx.ring[tail].upper.data & E1000_TXD_STAT_DD)) {
        cprintf("TX ring overflow\n");
        return 0;
    }

    /* fill in the next descriptor */
    memcpy(tx.data[tail], buf, len);
    /*
     * Set EOP to actually send this packet.
     * Set RS to get DD status bit when sent.
     */
    tx.ring[tail].lower.data = len | E1000_TXD_CMD_EOP | E1000_TXD_CMD_RS | E1000_TXD_CMD_IFCS;
    tx.ring[tail].upper.data = 0;

    /* move the tail pointer */
    e1000_write32(E1000_TDT, (tail + 1) % TX_RING_SIZE);

    return 0;
}

static int e1000_receive(char *buf, size_t len)
{
    unsigned int tail;

    if (!regs)
        return 0;

    tail = (e1000_read32(E1000_RDT) + 1) % RX_RING_SIZE;

    /* check if the descriptor has been filled */
    if (!(rx.ring[tail].status & E1000_RXD_STAT_DD))
        return 0;
    assert(rx.ring[tail].status & E1000_RXD_STAT_EOP, "end of packet");

    /* copy the packet data */
    len = min(len, (size_t)rx.ring[tail].length);
    memcpy(buf, rx.data[tail], len);
    rx.ring[tail].status = 0;

    /* move the tail pointer */
    e1000_write32(E1000_RDT, tail);

    return len;
}

static size_t find_pci(void)
{
    static const struct eerd eerd_e1000 = {
        .data_shift = 16, .addr_shift = 8, .done_bit = 0x00000010, .start_bit = 0x00000001,
    };
    /* PCIe */
    static const struct eerd eerd_e1000e = {
        .data_shift = 16, .addr_shift = 2, .done_bit = 0x00000002, .start_bit = 0x00000001,
    };
    size_t i;

    for (i = 0; i < NPCIDEV; ++i) {
        if (udevs[i].vendor != PCI_VENDOR_INTEL)
            continue;
        switch (udevs[i].product) {
        case PCI_PRODUCT_E1000_82540EM:
            eerd = &eerd_e1000;
            goto found;
        case PCI_PRODUCT_E1000_82574L:
            eerd = &eerd_e1000e;
            goto found;
        case PCI_PRODUCT_E1000_PCH_LPT_I217_LM:
            eerd = &eerd_e1000;
            goto found;
        }
    }
    if (i == NPCIDEV) {
        cprintf("ns: NIC driver not found, exiting...\n");
        exit();
    }

found:
    return i;
}

static void init_pci(void)
{
    pn_t root;

    /* [E1000 Table 4-2] BAR 0 gives the register base address */
    pci_index = find_pci();
    root = iommu_alloc_root(pci_index, UPCI_START, 0);
    regs = (void *)(uintptr_t)UPCI_START;

    iommu_map(root, &tx, sizeof(tx));
    iommu_map(root, &rx, sizeof(rx));
}

static uint16_t eeprom_read_16(size_t off)
{
    uint32_t val;
    size_t i;

    /* [E1000 13.4.4] Ensure EEC control is released */
    val = e1000_read32(E1000_EECD);
    val &= ~(E1000_EECD_REQ | E1000_EECD_GNT);
    e1000_write32(E1000_EECD, val);

    /* [E1000 5.3.1] Software EEPROM access */
    e1000_write32(E1000_EERD, (off << eerd->addr_shift) | eerd->start_bit);
    for (i = 0; i < 5; ++i) {
        val = e1000_read32(E1000_EERD);
        if (val & eerd->done_bit)
            return (val & E1000_EERD_DATA_MASK) >> eerd->data_shift;
    }
    assert(false, "eeprom read failed");
}

static void eeprom_read(uint16_t *buf, size_t off, size_t count)
{
    size_t i;

    for (i = 0; i < count; i++)
        buf[i] = eeprom_read_16(off + i);
}

static int detect_eeprom(void)
{
    uint32_t val;
    size_t i;

    e1000_write32(E1000_EERD, eerd->start_bit);
    for (i = 0; i < 1000; ++i) {
        val = e1000_read32(E1000_EERD);
        if (val & eerd->done_bit)
            return 1;
    }

    return 0;
}

static void read_mac(uint8_t *mac)
{
    size_t i;

    if (detect_eeprom()) {
        /* read mac address from EEPROM */
        cprintf("ns: MAC address in EEPROM\n");
        eeprom_read((void *)mac, EEPROM_OFF_MACADDR, 3);
        return;
    }
    cprintf("ns: MAC address not in EEPROM\n");

    /* EEPROM doesn't exist (e.g., I217) */
    for (i = 0; i < 6; ++i)
        mac[i] = mmio_read8(regs + E1000_RAL + i);
}

static void reset(void)
{
    uint32_t ctrl;

    /* [E1000e 14.4] Disable interrupts */
    e1000_write32(E1000_IMC, ~0U);

    /* [E1000e 14.5] Global reset */
    ctrl = e1000_read32(E1000_CTRL);
    e1000_write32(E1000_CTRL, ctrl | E1000_CTRL_RST);
    /* [E1000 13.4.1, E1000e 13.3.1] Delay 1 usec after reset */
    microdelay(1);

    /* [E1000e 14.4] Disable interrupts (again) */
    e1000_write32(E1000_IMC, ~0U);
}

static void init_link(void)
{
    /* [E1000 14.5.5, E1000e 14.8.2] MAC/PHY link setup */
    uint32_t ctrl;
    int i;

    ctrl = e1000_read32(E1000_CTRL);
    ctrl &= ~(E1000_CTRL_FRCSPD | E1000_CTRL_FRCDPX);
    ctrl |= E1000_CTRL_SLU;
    e1000_write32(E1000_CTRL, ctrl);

    cprintf("ns: waiting for link to come up\n");
    for (i = 0; i < 50; i++) {
        uint32_t status, speed;

        status = e1000_read32(E1000_STATUS);
        speed = status & E1000_STATUS_SPEED_MASK;
        if (status & E1000_STATUS_LU) {
            pr_info("ns: link up at %s Mb/s %s\n",
                    (speed == E1000_STATUS_SPEED_10) ? "10" :
                    (speed == E1000_STATUS_SPEED_100) ? "100" :
                    (speed == E1000_STATUS_SPEED_1000) ? "1000" : "unknown",
                    (status & E1000_STATUS_FD) ? "full-duplex" : "half-duplex");
            return;
        }
        microdelay(100000);
    }
    pr_info("ns: link did not come up\n");
    exit();
}

/* [E1000 14.5] Transmit initialization */
static void init_tx(void)
{
    size_t i;

    for (i = 0; i < TX_RING_SIZE; i++) {
        tx.ring[i].buffer_addr = (uintptr_t)tx.data[i];
        tx.ring[i].upper.fields.status = E1000_TXD_STAT_DD;
    }
    e1000_write32(E1000_TDBAH, (uintptr_t)tx.ring >> 32);
    e1000_write32(E1000_TDBAL, (uint32_t)(uintptr_t)tx.ring);
    static_assert(sizeof(tx.ring) % 128 == 0, "tx.ring size");
    e1000_write32(E1000_TDLEN, sizeof(tx.ring));
    e1000_write32(E1000_TDH, 0);
    e1000_write32(E1000_TDT, 0);
    e1000_flush();
    e1000_write32(E1000_TCTL, E1000_TCTL_EN | E1000_TCTL_PSP | (0x0f << E1000_TCTL_CT_SHIFT) |
                                        (0x3f << E1000_TCTL_COLD_SHIFT));
    e1000_write32(E1000_TIPG, 10 | (8 << 10) | (6 << 20));
}

/* [E1000 14.4] Receive initialization */
static void init_rx(void)
{
    size_t i;

    read_mac(mac);
    cprintf("ns: ether %02x:%02x:%02x:%02x:%02x:%02x\n", mac[0], mac[1], mac[2], mac[3], mac[4],
            mac[5]);

    for (i = 0; i < RX_RING_SIZE; i++) {
        rx.ring[i].buffer_addr = (uintptr_t)(rx.data[i]);
    }
    e1000_write32(E1000_RAL, (uint32_t)mac[0] | ((uint32_t)mac[1] << 8) |
                                      ((uint32_t)mac[2] << 16) | ((uint32_t)mac[3] << 24));
    e1000_flush();
    e1000_write32(E1000_RAH, E1000_RAH_AV | (uint32_t)mac[4] | ((uint32_t)mac[5] << 8));
    e1000_flush();
    for (i = 0; i < 4096 / 32; i++)
        e1000_write32(E1000_MTA + i * 4, 0);
    e1000_write32(E1000_IMS, 0);
    e1000_write32(E1000_RDBAL, (uint32_t)(uintptr_t)rx.ring);
    e1000_write32(E1000_RDBAH, (uintptr_t)rx.ring >> 32);
    static_assert(sizeof(rx.ring) % 128 == 0, "rx.ring size");
    e1000_write32(E1000_RDLEN, sizeof(rx.ring));
    e1000_write32(E1000_RDH, 0);
    e1000_write32(E1000_RDT, RX_RING_SIZE - 1);
    e1000_flush();
    /* strip CRC */
    e1000_write32(E1000_RCTL,
                 E1000_RCTL_EN | E1000_RCTL_BAM | E1000_RCTL_SZ_2048 | E1000_RCTL_SECRC);
}

static void irq_handler(void)
{
    e1000_read32(E1000_ICR);
}

uint32_t pci_conf_read(uint16_t devid, uint32_t off)
{
    return mmio_read32(uecam + devid * PAGE_SIZE + off);
}

void pci_conf_write(uint16_t devid, uint32_t off, uint32_t v)
{
    return mmio_write32(uecam + devid * PAGE_SIZE + off, v);
}

static int init_ecam(void)
{
    physaddr_t pci_config_base;
    size_t i;

    pci_config_base = sys_debug_sysctl(SYSCTL_ECAM_ADDRESS);
    if (pci_config_base == 0 || pci_config_base == UINT64_MAX)
        return -ENODEV;

    for (i = 0; i < NPCIDEV; ++i) {
        devid_t devid = udevs[i].devid;
        uintptr_t va = UECAM_START + devid * PAGE_SIZE;
        pte_t perm = PTE_P | PTE_W | PTE_PWT | PTE_PCD;

        sys_map_pcipage(page_walk(va), PT_INDEX(va), pfn_to_pcipn(pci_config_base / PAGE_SIZE + devid), perm);
    }
    return 0;
}

static int is_ecam_mapped(devid_t devid)
{
    return is_page_mapped(UECAM_START + devid * PAGE_SIZE);
}

static int init_msi(devid_t devid, size_t index)
{
    uint32_t reg, off;
    uint16_t vendor;

    reg = pci_conf_read(devid, PCI_COMMAND_STATUS_REG);
    if (!(reg & PCI_STATUS_CAPLIST_SUPPORT)) {
        pr_info("ns: no caplist\n");
        return -ENODEV;
    }

    reg = pci_conf_read(devid, PCI_CAPLISTPTR_REG);
    for (off = PCI_CAPLIST_PTR(reg); off; off = PCI_CAPLIST_NEXT(reg)) {
        reg = pci_conf_read(devid, off);
        if (PCI_CAPLIST_CAP(reg) == PCI_CAP_MSI)
            break;
    }

    if (!off) {
        pr_info("ns: no MSI\n");
        return -ENODEV;
    }
    assert(reg & PCI_MSI_CTL_64BIT_ADDR, "must support 64-bit addresses");
    assert(PCI_MSI_CTL_MMC(reg) == 0, "1 requested vector only");

    vendor = sys_debug_sysctl(SYSCTL_IOMMU_VENDOR);
    switch (vendor) {
    case PCI_VENDOR_INTEL:
        /* message address */
        pci_conf_write(devid, off + 4 * 1,
                       (0x0fee << 20) | /* magic number */
                       BIT32(4) |       /* remappable format */
                       BIT32(3) |       /* SHV */
                       ((index & 0x7fff) << 5) | ((index >> 15) << 2));
        pci_conf_write(devid, off + 4 * 2, 0);
        /* message data */
        pci_conf_write(devid, off + 4 * 3, 0);
        break;
#if 0
    case PCI_VENDOR_AMD:
        /* message data [10:0] */
        assert(index < SZ_1K, "index too large");
        pci_conf_write(devid, off + 4 * 3, index);
        break;
#endif
    default:
        pr_info("ns: no interrupt support for IOMMU vendor 0x%04x\n", vendor);
        return -ENODEV;
    }

    /* enable MSI */
    pci_conf_write(devid, off, reg | PCI_MSI_CTL_MSI_ENABLE);
    pr_info("ns: MSI enabled\n");
    return 0;
}

static void init_irq(void)
{
    /* hardcode index and vector as no one else is using it now */
    size_t index = 0;
    uint8_t vector = TRAP_USER;
    devid_t devid = udevs[pci_index].devid;
    int r;

    if (init_ecam())
        return;

    if (!is_ecam_mapped(devid)) {
        cprintf("ECAM not mapped for PCI device %x\n", devid);
        return;
    }

    r = sys_alloc_vector(vector);
    assert(r == 0, "sys_alloc_vector");

    r = sys_alloc_intremap(index, devid, vector);
    assert(r == 0, "sys_alloc_intremap");

    if (init_msi(devid, index))
        return;

#if 0
    e1000_write32(E1000_IMC, ~BIT32(0));
    e1000_flush();
    /* rx overrun and timer */
    e1000_write32(E1000_IMS, E1000_ICR_RXO | E1000_ICR_RXT0);
    e1000_flush();
#endif
}

static void init_timer(void)
{
    pid_t pid;

    pid = spawnl("timer", "timer", STRINGIFY(NSPID), NULL);
    assert(pid > 0, "timer failed");
}

static err_t low_level_output(struct netif *netif, struct pbuf *p)
{
    struct pbuf *q;
    int r;

    for (q = p; q != NULL; q = q->next) {
        r = e1000_transmit(q->payload, q->len);
        assert(r == 0, "e1000_transmit");
    }
    return ERR_OK;
}

static err_t e1000_init(struct netif *netif)
{
    netif->name[0] = 'e';
    netif->name[1] = 'h';
    netif->output = etharp_output;
    netif->linkoutput = low_level_output;
    netif->hwaddr_len = ETHARP_HWADDR_LEN;
    memcpy(netif->hwaddr, mac, ETHARP_HWADDR_LEN);
    netif->mtu = 1500;
    netif->flags = NETIF_FLAG_BROADCAST | NETIF_FLAG_ETHARP | NETIF_FLAG_ETHERNET;
    return ERR_OK;
}

static void init_netif(struct netif *netif)
{
    char ip[IP4ADDR_STRLEN_MAX], netmask[IP4ADDR_STRLEN_MAX], gw[IP4ADDR_STRLEN_MAX];

    lwip_init();

    netif_add(netif, IP4_ADDR_ANY, IP4_ADDR_ANY, IP4_ADDR_ANY, NULL, e1000_init, netif_input);
    netif_set_default(netif);
    netif_set_link_up(netif);
    netif_set_up(netif);

    dhcp_start(netif);
    cprintf("ns: dhcp initializing\n");
    while (!dhcp_supplied_address(netif))
        do_timer(0);

    ip4addr_ntoa_r(netif_ip4_addr(netif), ip, sizeof(ip));
    ip4addr_ntoa_r(netif_ip4_netmask(netif), netmask, sizeof(netmask));
    ip4addr_ntoa_r(netif_ip4_gw(netif), gw, sizeof(gw));
    cprintf("ns: inet %s netmask %s broadcast %s\n", ip, netmask, gw);
}

static struct socket *fd_lookup(pid_t pid, int fd)
{
    fn_t fn;
    int i;
    struct file *f;
    struct socket *socket;

    if (!is_fd_valid(fd))
        goto notfound;
    fn = uprocs[pid].ofile[fd];
    if (!is_fn_valid(fn))
        goto notfound;
    /* check own ofile for fd */
    for (i = 0; i < NOFILE; ++i) {
        if (ucurrent->ofile[i] == fn)
            break;
    }
    if (i == NOFILE)
        goto notfound;
    f = &ufiles[fn];
    if (f->type != FD_SOCKET) {
        cprintf("ns: pid %ld fd %d is type %ld, not a socket\n", pid, fd, f->type);
        goto notfound;
    }
    socket = (void *)(uintptr_t)f->value;
    assert(socket->fd == i, "fd must match");
    return socket;

notfound:
    cprintf("ns: pid %ld fd %d not found\n", pid, fd);
    return NULL;
}
