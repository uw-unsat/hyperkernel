#pragma once

#include <uapi/cdefs.h>

struct trap_regs;

void hvm_init(void);
extern void (*hvm_user_init)(void *hvm, register_t rip);
extern void (*hvm_switch)(void *hvm, void *stack, register_t cr3, timer_t timer, int launched);
extern void (*hvm_flush)(void *hvm);
extern void (*hvm_copy)(void *dst, void *src, pid_t pid);
extern void (*hvm_set_timer)(void *hvm, timer_t timer);
extern void (*hvm_set_io_bitmap)(void *hvm, void *addr);
extern void (*hvm_set_pid)(void *hvm, pid_t pid);
extern void (*hvm_invalidate_tlb)(pid_t pid);

/* callback into OS */
extern void (*hvm_preempt)(void);
extern void (*hvm_fault)(void);
extern int (*hvm_extintr)(uint8_t irq);
