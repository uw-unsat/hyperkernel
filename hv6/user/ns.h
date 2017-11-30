#pragma once

#include "user.h"

enum {
    NSIPC_TIMER = 1,
    NSIPC_GETHOSTBYNAME,
    NSIPC_SOCKET,
    NSIPC_GETSOCKOPT,
    NSIPC_CONNECT,
    NSIPC_BIND,
    NSIPC_LISTEN,
    NSIPC_ACCEPT,
    NSIPC_SEND,
    NSIPC_RECV,
};

struct nsipc_ping {
    union {
        struct {
            int domain;
            int type;
            int protocol;
        } socket;
        struct {
            int sockfd;
            int level;
            int optname;
        } getsockopt;
        struct {
            int sockfd;
            uint32_t addr;
            uint16_t port;
        } connect;
        struct {
            int sockfd;
            uint32_t addr;
            uint16_t port;
        } bind;
        struct {
            int sockfd;
            int backlog;
        } listen;
        struct {
            int sockfd;
        } accept;
        struct {
            int sockfd;
            int flags;
            char buf[];
        } send;
        struct {
            int sockfd;
            int len;
            int flags;
        } recv;
    };
};

struct nsipc_pong {
    union {
        struct {
            uint32_t addr;
            uint16_t port;
        } accept;
    };
};
