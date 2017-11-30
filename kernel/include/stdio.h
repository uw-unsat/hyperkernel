#pragma once

#include <uapi/cdefs.h>

void putchar(int c);
void puts(const char *s);

int kvprintf(const char *fmt, void (*func)(int, void *), void *arg, va_list ap) __printf(1, 0);
int printf(const char *fmt, ...) __printf(1, 2);
int vprintf(const char *fmt, va_list ap) __printf(1, 0);
int snprintf(char *str, size_t size, const char *fmt, ...) __printf(3, 4);
int vsnprintf(char *str, size_t size, const char *fmt, va_list ap) __printf(3, 0);

int getchar(void);
