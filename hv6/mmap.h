#pragma once
#include "types.h"

int sys_mmap_page(uintptr_t va, pte_t perm);
int sys_munmap_page(uintptr_t va);
