#include <uapi/console.h>
#include <uapi/errno.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

static int logpriority = LOG_DEBUG;
static int lognewline = 1;

/* kernel log ring buffer */
static char klog_buf[KLOG_NR_LINES][KLOG_LINE_SIZE];
static size_t klog_line;

static void putch(int c, void *arg)
{
    int *newline = arg, len;
    static char line_buf[KLOG_LINE_SIZE];
    static size_t line_size;

    if (*newline) {
        nanoseconds_t up = uptime();
        uint64_t s = up / 1000000000;
        uint64_t ms = (up / 1000) % 1000000;

        *newline = 0;
        /* [seconds.microseconds] */
        bzero(line_buf, KLOG_LINE_SIZE);
        len = snprintf(line_buf, KLOG_LINE_SIZE, "[%5" PRIu64 ".%06" PRIu64 "] ", s, ms);
        console_write(line_buf, len);
        line_size = len;
    }

    putchar(c);

    assert(line_size < KLOG_LINE_SIZE, "line too long");
    line_buf[line_size] = (uint8_t)c;
    ++line_size;

    if (c == '\n') {
        *newline = 1;
        memcpy(klog_buf[klog_line % KLOG_NR_LINES], line_buf, KLOG_LINE_SIZE);
        ++klog_line;
    }
}

void syslog(int priority, const char *fmt, ...)
{
    va_list ap;

    va_start(ap, fmt);
    vsyslog(priority, fmt, ap);
    va_end(ap);
}

void vsyslog(int priority, const char *fmt, va_list ap)
{
    if (priority > logpriority)
        return;
    kvprintf(fmt, putch, &lognewline, ap);
}

int syslog_read(void *dest, size_t n, size_t off)
{
    size_t i, start, len;
    const char *line_buf;

    /* log has wrapped around: start from klog_line rather than 0 */
    if (klog_line >= KLOG_NR_LINES)
        start = klog_line;
    else
        start = 0;

    for (i = 0; i < KLOG_NR_LINES; ++i) {
        line_buf = klog_buf[(start + i) % KLOG_NR_LINES];
        len = strnlen(line_buf, KLOG_LINE_SIZE);
        if (off < len) {
            memcpy(dest, line_buf + off, len - off);
            return len - off;
        }
        off -= len;
    }

    return 0;
}
