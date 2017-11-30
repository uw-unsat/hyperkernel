#pragma once

#include <uapi/machine/trap_assym.h>

.macro	SAVE_RAX_REG offset=0
	movq	%rax, TRAP_REGS_RAX+\offset(%rsp)
.endm

.macro	LOAD_RAX_REG offset=0
	movq	TRAP_REGS_RAX+\offset(%rsp), %rax
.endm

.macro	SAVE_C_REGS offset=0 rax=1 rcx=1 rdx=1
	.if \rax
	SAVE_RAX_REG \offset
	.endif
	movq	%r11, TRAP_REGS_R11+\offset(%rsp)
	movq	%r10, TRAP_REGS_R10+\offset(%rsp)
	movq	%r9, TRAP_REGS_R9+\offset(%rsp)
	movq	%r8, TRAP_REGS_R8+\offset(%rsp)
	.if \rcx
	movq	%rcx, TRAP_REGS_RCX+\offset(%rsp)
	.endif
	.if \rdx
	movq	%rdx, TRAP_REGS_RDX+\offset(%rsp)
	.endif
	movq	%rsi, TRAP_REGS_RSI+\offset(%rsp)
	movq	%rdi, TRAP_REGS_RDI+\offset(%rsp)
.endm

.macro	LOAD_C_REGS offset=0 rax=1 rcx=1 rdx=1
	.if \rax
	LOAD_RAX_REG \offset
	.endif
	movq	TRAP_REGS_R11+\offset(%rsp), %r11
	movq	TRAP_REGS_R10+\offset(%rsp), %r10
	movq	TRAP_REGS_R9+\offset(%rsp), %r9
	movq	TRAP_REGS_R8+\offset(%rsp), %r8
	.if \rcx
	movq	TRAP_REGS_RCX+\offset(%rsp), %rcx
	.endif
	.if \rdx
	movq	TRAP_REGS_RDX+\offset(%rsp), %rdx
	.endif
	movq	TRAP_REGS_RSI+\offset(%rsp), %rsi
	movq	TRAP_REGS_RDI+\offset(%rsp), %rdi
.endm

.macro	SAVE_C_REGS_EXCEPT_RAX offset=0
	SAVE_C_REGS \offset rax=0
.endm

.macro	LOAD_C_REGS_EXCEPT_RAX offset=0
	LOAD_C_REGS \offset rax=0
.endm

.macro	SAVE_C_REGS_EXCEPT_RAX_RCX_RDX offset=0
	SAVE_C_REGS \offset rax=0 rcx=0 rdx=0
.endm

.macro	LOAD_C_REGS_EXCEPT_RAX_RCX_RDX offset=0
	LOAD_C_REGS \offset rax=0 rcx=0 rdx=0
.endm

.macro	SAVE_EXTRA_REGS offset=0
	movq	%r15, TRAP_REGS_R15+\offset(%rsp)
	movq	%r14, TRAP_REGS_R14+\offset(%rsp)
	movq	%r13, TRAP_REGS_R13+\offset(%rsp)
	movq	%r12, TRAP_REGS_R12+\offset(%rsp)
	movq	%rbp, TRAP_REGS_RBP+\offset(%rsp)
	movq	%rbx, TRAP_REGS_RBX+\offset(%rsp)
.endm

.macro	LOAD_EXTRA_REGS offset=0
	movq	TRAP_REGS_R15+\offset(%rsp), %r15
	movq	TRAP_REGS_R14+\offset(%rsp), %r14
	movq	TRAP_REGS_R13+\offset(%rsp), %r13
	movq	TRAP_REGS_R12+\offset(%rsp), %r12
	movq	TRAP_REGS_RBP+\offset(%rsp), %rbp
	movq	TRAP_REGS_RBX+\offset(%rsp), %rbx
.endm

/* TODO: use xsave */
.macro	SAVE_FPU_REGS offset=0
#if ENABLED(CONFIG_FPU)
	fxsaveq		TRAP_REGS_SIZE+\offset(%rsp)
#endif
.endm

/* TODO: use xrstor */
.macro	LOAD_FPU_REGS offset=0
#if ENABLED(CONFIG_FPU)
	fxrstorq	TRAP_REGS_SIZE+\offset(%rsp)
#endif
.endm
