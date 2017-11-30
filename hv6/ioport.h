#pragma once

#include "proc.h"

int sys_alloc_io_bitmap(pn_t pn1, pn_t pn2, pn_t pn3);
int sys_alloc_port(uint16_t port);
int sys_reclaim_port(uint16_t port);

/* kernel will reserve certain ports */
void reserve_port(uint16_t port);
void reserve_ports(uint16_t port, size_t n);
void allow_port(uint16_t port);
void allow_ports(uint16_t port, size_t n);
