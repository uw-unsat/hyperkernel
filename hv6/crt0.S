#include <uapi/machine/mmu.h>

.section .text

.global	_start
_start:
	movq	$0, %rbp
	pop	%rdi		/* argc */
	movq	%rsp, %rsi	/* argv */
	push	%rbp		/* align the stack */
	call	main
spin:
	call	exit
	jmp	spin
