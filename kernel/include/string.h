#pragma once

#include <uapi/cdefs.h>

void *memchr(const void *s, int c, size_t n);
int memcmp(const void *s1, const void *s2, size_t n);
void *memmove(void *dst, const void *src, size_t n);
void *memcpy(void *restrict dst, const void *restrict src, size_t n);
void *memset(void *s, int c, size_t n);
void bzero(void *s, size_t n);

size_t strlen(const char *s);
size_t strnlen(const char *s, size_t maxlen);
char *strchr(const char *s, int c);
int strcmp(const char *s1, const char *s2);
int strncmp(const char *s1, const char *s2, size_t n);
char *strcpy(char *restrict to, const char *restrict from);
char *strncpy(char *restrict dst, const char *restrict src, size_t n);
char *strcat(char *restrict s, const char *restrict append);
char *strsep(char **stringp, const char *delim);
