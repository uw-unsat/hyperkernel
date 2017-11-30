#include <uapi/machine/cpufunc.h>
#include <uapi/machine/io.h>
#include <uapi/console.h>
#include <string.h>

#define BACKSPACE 0x100

static void cga_putc(void *arg, int c)
{
    uint16_t *crt = arg;
    int pos;

    /* cursor position: col + 80*row */
    outb(PORT_CRT, 14);
    pos = inb(PORT_CRT + 1) << 8;
    outb(PORT_CRT, 15);
    pos |= inb(PORT_CRT + 1);

    if (c == '\n') {
        pos += 80 - pos % 80;
    } else if (c == BACKSPACE) {
        if (pos > 0)
            --pos;
    } else {
        crt[pos++] = (c & 0xff) | 0x0700; /* black on white */
    }

    if (pos < 0 || pos > 25 * 80)
        panic("pos under/overflow");

    if (pos / 80 >= 24) { /* scroll up */
        memmove(crt, crt + 80, sizeof(crt[0]) * 23 * 80);
        pos -= 80;
        memset(crt + pos, 0, sizeof(crt[0]) * (24 * 80 - pos));
    }

    outb(PORT_CRT, 14);
    outb(PORT_CRT + 1, pos >> 8);
    outb(PORT_CRT, 15);
    outb(PORT_CRT + 1, pos);
    crt[pos] = ' ' | 0x0700;
}

void cga_write(void *arg, const char *s, size_t n)
{
    size_t i;

    for (i = 0; i < n; ++i)
        cga_putc(arg, (uint8_t)s[i]);
}

void cga_init(void *arg)
{
#if ENABLED(CONFIG_CGA)
    static struct console_device dev = {
        .write = cga_write,
    };

    dev.arg = arg;
    console_register(&dev);
#endif
}
