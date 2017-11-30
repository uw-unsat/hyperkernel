#pragma once

#include <uapi/machine/trap.h>

struct env {
    /* Root container of this environment */
    struct container *container;
    /* Current program counter */
    uint64_t pc;
    void *pgdir;
    struct trap_regs regs;
};
