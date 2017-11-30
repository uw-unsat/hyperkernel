#pragma once

/* no threads, semaphores, mutexes, mboxes */
#define NO_SYS 1

#define SYS_LIGHTWEIGHT_PROT 0

#define LWIP_NETCONN 0
#define LWIP_SOCKET 0

#define LWIP_ARP 1
#define LWIP_DHCP 1
#define LWIP_DNS 1
#define LWIP_ETHERNET 1

#define LWIP_DEBUG 1
#if 0
#define DHCP_DEBUG LWIP_DBG_ON
#define NETIF_DEBUG LWIP_DBG_ON
#define TCP_OUTPUT_DEBUG LWIP_DBG_ON
#endif

#define LWIP_EVENT_API 1

#define TCP_LISTEN_BACKLOG 1

#define SO_REUSE 1
