#pragma once

#ifndef __ASSEMBLER__
#error "Must be included from assembly code"
#endif

#include <uapi/machine/trap_support.h>
#include <uapi/errno.h>
#include <uapi/syscall.h>

/* %rax holds the syscall number; use %r10-r11 as scratch registers */
.macro	INVOKE_SYSCALL
	/* validate the syscall number */
	cmpq	$NR_syscalls, %rax
	jb	1f
	movq	$-ENOSYS, %rax
	jmp	2f
1:
	movq	$syscalls, %r10
	leaq	(%r10, %rax, 8), %rax
	/* invoke the syscall */
	callq	*(%rax)
2:
.endm
