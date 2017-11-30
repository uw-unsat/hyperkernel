#include <uapi/machine/cpufunc.h>
#include <uapi/console.h>

static void porte9_write(void *arg, const char *s, size_t n)
{
    outsb(0xe9, s, n);
}

static struct console_device dev = {
    .write = porte9_write,
};

void porte9_init(void)
{
    console_register(&dev);
}
