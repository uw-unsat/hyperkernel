#pragma once

#include <container.h>

int pagemap_insert(struct capability pagemap, struct capability item, uintptr_t addr,
                   unsigned flags);
