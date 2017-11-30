#include <uapi/machine/cpufunc.h>

void panic(const char *fmt, ...)
{
    va_list ap;

    va_start(ap, fmt);
    if (fmt) {
        pr_crit("kernel panic: ");
        vsyslog(LOG_CRIT, fmt, ap);
        pr_crit("\n");
    }
    va_end(ap);

    /* QEMU's -isa-debug-exit */
    outb(0x501, 0);
    /* Bochs shutdown port */
    outsb(0x8900, "Shutdown", 8);

    while (1)
        halt();
}
