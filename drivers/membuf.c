#include <uapi/console.h>
#include <string.h>

#define BACKSPACE 0x08
#define DELETE 0x7f

static uint8_t buf[80 * 25];
static int pos;

static void membuf_putc(uint8_t c)
{
    if (c == '\n') {
        pos += 80 - pos % 80;
    } else if (c == '\r') {
        /* do nothing */
    } else if (c == BACKSPACE || c == DELETE) {
        if (pos > 0)
            --pos;
    } else {
        buf[pos++] = c;
    }

    if (pos < 0 || pos > 25 * 80)
        panic("pos under/overflow");

    if (pos / 80 >= 24) { /* scroll up */
        memmove(buf, buf + 80, 23 * 80);
        pos -= 80;
        memset(buf + pos, 0, 24 * 80 - pos);
    }
}

static void membuf_write(void *arg, const char *s, size_t n)
{
    size_t i;
    int escape = 0;

    for (i = 0; i < n; ++i) {
        uint8_t c = s[i];

        if (escape) {
            if (c == 'm')
                escape = 0;
            continue;
        }
        if (c == '\x1b') {
            escape = 1;
            continue;
        }
        membuf_putc(c);
    }
}

int membuf_get(void *s)
{
    memcpy(s, buf, sizeof(buf));
    return pos;
}

void membuf_init(void)
{
    static struct console_device dev = {
        .write = membuf_write,
    };

    console_register(&dev);
}
