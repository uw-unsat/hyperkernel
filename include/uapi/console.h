#pragma once

#include <uapi/queue.h>

struct console_device {
    void *arg;
    int (*getc)(void *);
    void (*write)(void *, const char *, size_t);

    SLIST_ENTRY(console_device) link;
};

int console_getc(void);
void console_write(const char *s, size_t n);
void console_register(struct console_device *dev);

void uart8250_init(void);
void porte9_init(void);
void kbd_init(void);
void cga_init(void *);
void cga_write(void *arg, const char *s, size_t n);
void membuf_init(void);
int membuf_get(void *);
