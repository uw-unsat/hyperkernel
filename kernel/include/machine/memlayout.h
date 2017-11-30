#pragma once

#include <uapi/machine/mmu.h>
#include <symtable.h>

#define TEXT_OFFSET SZ_2M

/* kernel stack */
#define STACK_SIZE (2 * PAGE_SIZE)

#define GDT_ENTRY_CS 1
#define GDT_ENTRY_DS 2
/* TSS selector takes up two slots */
#define GDT_ENTRY_TSS 3

#define GDT_CS (GDT_ENTRY_CS << 3)
#define GDT_DS (GDT_ENTRY_DS << 3)
#define GDT_TSS (GDT_ENTRY_TSS << 3)
