#include "ns.h"

static uint8_t ping_buf[PAGE_SIZE] __aligned(PAGE_SIZE);
static struct fsipc_ping *ping = (void *)ping_buf;

int main(int argc, char **argv)
{
    pid_t pid;

    assert(argc >= 2, "usage: timer pid");

    pid = atoi(argv[1]);

    while (1) {
        sys_send(pid, NSIPC_TIMER, virt_to_pn(ping), 0, -1);
        /* TODO: sleep */
        yield();
    }

    exit();
}
