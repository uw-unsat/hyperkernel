#include "memlayout.h"

.section .text

.global	_start
_start:
	movq	$stack_top, %rsp
	/* ulib entry point */
	movq	$0xffffffff80000000, %rax
	call	*%rax
	/* return from ulib_init */
	call	main
spin:
	jmp	spin

.section .bss
.balign	PAGE_SIZE
	.space	USTACK_SIZE
stack_top:
