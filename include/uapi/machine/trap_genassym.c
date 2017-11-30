#include <uapi/assym.h>
#include "trap.h"

ASSYM(TRAP_REGS_R15, offsetof(struct trap_regs, r15));
ASSYM(TRAP_REGS_R14, offsetof(struct trap_regs, r14));
ASSYM(TRAP_REGS_R13, offsetof(struct trap_regs, r13));
ASSYM(TRAP_REGS_R12, offsetof(struct trap_regs, r12));
ASSYM(TRAP_REGS_RBP, offsetof(struct trap_regs, rbp));
ASSYM(TRAP_REGS_RBX, offsetof(struct trap_regs, rbx));
ASSYM(TRAP_REGS_RAX, offsetof(struct trap_regs, rax));
ASSYM(TRAP_REGS_R11, offsetof(struct trap_regs, r11));
ASSYM(TRAP_REGS_R10, offsetof(struct trap_regs, r10));
ASSYM(TRAP_REGS_R9, offsetof(struct trap_regs, r9));
ASSYM(TRAP_REGS_R8, offsetof(struct trap_regs, r8));
ASSYM(TRAP_REGS_RCX, offsetof(struct trap_regs, rcx));
ASSYM(TRAP_REGS_RDX, offsetof(struct trap_regs, rdx));
ASSYM(TRAP_REGS_RSI, offsetof(struct trap_regs, rsi));
ASSYM(TRAP_REGS_RDI, offsetof(struct trap_regs, rdi));
ASSYM(TRAP_REGS_SIZE, sizeof(struct trap_regs));
