#pragma once

#include <uapi/cdefs.h>

#define BOOTMEM_MAP_MAX_SIZE 128

struct region {
    physaddr_t lower, upper; /* [lower, upper) */
};

struct bootmem_map {
    size_t size;
    struct region regions[BOOTMEM_MAP_MAX_SIZE];
};

extern struct bootmem_map bootmem_map;

void bootmem_add(physaddr_t addr, size_t size);
void bootmem_remove(physaddr_t addr, size_t size);
bool bootmem_usable(physaddr_t addr, size_t size);
void *bootmem_alloc(size_t alignment, size_t size);
void bootmem_seal(void);
