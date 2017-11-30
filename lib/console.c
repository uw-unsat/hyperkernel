#include <uapi/console.h>

#define CONSBUFSIZ 512

static struct {
    uint8_t buf[CONSBUFSIZ];
    size_t rpos;
    size_t wpos;
} queue;

static SLIST_HEAD(console_list, console_device) devs;

static void console_intr(int (*proc)(void *), void *arg)
{
    int c;

    while ((c = (*proc)(arg)) >= 0) {
        if (c == 0)
            continue;
        queue.buf[queue.wpos++] = c;
        if (queue.wpos == CONSBUFSIZ)
            queue.wpos = 0;
    }
}

int console_getc(void)
{
    struct console_device *dev;

    SLIST_FOREACH(dev, &devs, link)
    {
        if (dev->getc)
            console_intr(dev->getc, dev->arg);
    }

    if (queue.rpos != queue.wpos) {
        int c = queue.buf[queue.rpos++];

        if (queue.rpos == CONSBUFSIZ)
            queue.rpos = 0;
        return c;
    }

    return 0;
}

void console_write(const char *s, size_t n)
{
    struct console_device *dev;

    SLIST_FOREACH(dev, &devs, link)
    {
        if (dev->write)
            dev->write(dev->arg, s, n);
    }
}

void console_register(struct console_device *dev)
{
    SLIST_INSERT_HEAD(&devs, dev, link);
}
