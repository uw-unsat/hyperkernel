#pragma once

#include <uapi/cdefs.h>

#define IRQ_TIMER               0
#define IRQ_KBD                 1
#define IRQ_COM2                3
#define IRQ_COM1                4
#define IRQ_ERROR               19
#define IRQ_SPURIOUS            31

#define PORT_COM2               0x2f8
#define PORT_COM1               0x3f8

#define PORT_KBD_DATA           0x60
#define PORT_KBD_STATUS         0x64

#define PORT_CRT                0x3d4

#define PORT_PCI_CONF_ADDRESS   0xcf8
#define PORT_PCI_CONF_DATA      0xcfc

#define CGA_START               UINT64_C(0xb8000)

#define VRAM_START              UINT64_C(0xa0000)
#define VRAM_END                UINT64_C(0xbffff)

/*
 * 0xc0000000 might be good enough: ECAM often starts at 0xf000xxxx,
 * but it's 0xa0000000 on sysv (0xb0000000 on QEMU), therefore the value.
 */
#define PCI_START               UINT64_C(0xa0000000)
#define PCI_END                 UINT64_C(0x100000000)
