#pragma once

#include "types.h"

struct hostent {
    char *h_name;             /* official name of host */
    char **h_aliases;         /* alias list */
    int h_addrtype;           /* host address type */
    int h_length;             /* length of address */
    char **h_addr_list;       /* list of addresses from name server */
#define h_addr h_addr_list[0] /* address, for backward compatibility */
};

struct in_addr {
    uint32_t s_addr;
};

struct sockaddr {
    uint8_t sa_len;
    uint8_t sa_family;
    char sa_data[14];
};

struct sockaddr_in {
    uint8_t sin_len;
    uint8_t sin_family;
    uint16_t sin_port;
    struct in_addr sin_addr;
    char sin_zero[8];
};

char *inet_ntoa(struct in_addr in);
char *inet_ntoa_r(struct in_addr in, char *buf, socklen_t size);

struct hostent *gethostbyname(const char *name);

int socket(int domain, int type, int protocol);
int getsockopt(int sockfd, int level, int optname, void *optval, socklen_t *optlen);
int connect(int sockfd, const struct sockaddr *addr, socklen_t addrlen);
int bind(int sockfd, const struct sockaddr *addr, socklen_t addrlen);
int listen(int sockfd, int backlog);
int accept(int sockfd, struct sockaddr *addr, socklen_t *addrlen);
ssize_t send(int sockfd, const void *buf, size_t len, int flags);
ssize_t sendto(int sockfd, const void *buf, size_t len, int flags, const struct sockaddr *dest_addr,
               socklen_t addrlen);
ssize_t recv(int sockfd, void *buf, size_t len, int flags);
ssize_t recvfrom(int sockfd, void *buf, size_t len, int flags, struct sockaddr *src_addr,
                 socklen_t *addrlen);

#ifdef htons
#undef htons
#endif
#define htons __builtin_bswap16

#ifdef ntohs
#undef ntohs
#endif
#define ntohs __builtin_bswap16

#ifdef htonl
#undef htonl
#endif
#define htonl __builtin_bswap32

#ifdef ntohl
#undef ntohl
#endif
#define ntohl __builtin_bswap32

#ifndef INADDR_ANY
#define INADDR_ANY 0
#endif
