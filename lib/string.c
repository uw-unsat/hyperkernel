#include <string.h>

void *memchr(const void *s, int c, size_t n)
{
    if (n != 0) {
        const unsigned char *p = s;

        do {
            if (*p++ == (unsigned char)c)
                return ((void *)(uintptr_t)(p - 1));
        } while (--n != 0);
    }
    return NULL;
}

int memcmp(const void *s1, const void *s2, size_t n)
{
    if (n != 0) {
        const unsigned char *p1 = s1, *p2 = s2;

        do {
            if (*p1++ != *p2++)
                return (*--p1 - *--p2);
        } while (--n != 0);
    }

    return 0;
}

void *memmove(void *dst, const void *src, size_t n)
{
    const char *s = src;
    char *d = dst;

    if (s < d && s + n > d) {
        s += n;
        d += n;
        while (n-- > 0)
            *--d = *--s;
    } else {
        while (n-- > 0)
            *d++ = *s++;
    }

    return dst;
}

void *memcpy(void *restrict dst, const void *restrict src, size_t n)
{
    char *d = dst;
    const char *s = src;

    while (n-- > 0)
        *d++ = *s++;
    return d;
}

void *memset(void *s, int c, size_t n)
{
    char *p = s;

    while (n-- > 0)
        *p++ = c;
    return s;
}

void bzero(void *s, size_t n)
{
    memset(s, 0, n);
}

size_t strlen(const char *s)
{
    size_t n;

    for (n = 0; s[n]; ++n)
        ;
    return n;
}

size_t strnlen(const char *s, size_t maxlen)
{
    size_t len;

    for (len = 0; len < maxlen; len++, s++) {
        if (!*s)
            break;
    }
    return len;
}

char *strchr(const char *s, int c)
{
    for (; *s; ++s) {
        if (*s == c)
            return (char *)s;
    }
    return NULL;
}

int strcmp(const char *s1, const char *s2)
{
    for (; *s1 && *s1 == *s2; ++s1, ++s2)
        ;
    return (int)((unsigned char)*s1 - (unsigned char)*s2);
}

int strncmp(const char *s1, const char *s2, size_t n)
{
    for (; n > 0 && *s1 && *s1 == *s2; n--, s1++, s2++)
        ;
    if (n == 0)
        return 0;
    else
        return (int)((unsigned char)*s1 - (unsigned char)*s2);
}

char *strcpy(char *restrict to, const char *restrict from)
{
    char *save = to;

    for (; (*to = *from) != 0; ++from, ++to)
        ;
    return save;
}

char *strncpy(char *restrict dst, const char *restrict src, size_t n)
{
    size_t i;
    char *retval = dst;

    for (i = 0; i < n; ++i) {
        *dst++ = *src;
        /* NULL pad the remaining bytes */
        if (*src != 0)
            ++src;
    }
    return retval;
}

char *strcat(char *restrict s, const char *restrict append)
{
    char *save = s;

    for (; *s; ++s)
        ;
    while ((*s++ = *append++) != 0)
        ;
    return save;
}

char *strsep(char **stringp, const char *delim)
{
    char *s;
    char *retval = *stringp;

    for (s = *stringp; *s; ++s) {
        if (strchr(delim, *s)) {
            *s = 0;
            *stringp = s + 1;
            return retval;
        }
    }
    *stringp = NULL;
    return retval;
}
