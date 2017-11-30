#include <uapi/machine/mmu.h>

.section .head.text

.global	_start
_start:
	push	%rbp
	movq	%rsp, %rbp
	movq	$ulib_stack_top, %rsp
	call	ulib_init
	movq	%rbp, %rsp
	pop	%rbp
	ret

.section .bss
.balign	PAGE_SIZE
.global	ulib_stack_top
	.space	SZ_64K
ulib_stack_top:
