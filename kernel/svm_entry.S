#include <machine/memlayout.h>
#include "hvm_support.S"
#include "svm.h"
#include "svm_assym.h"

.global	svm_loop
svm_loop:
	LOAD_FPU_REGS
	LOAD_EXTRA_REGS
	LOAD_RAX_REG

svm_fast_path:
	LOAD_C_REGS_EXCEPT_RAX
	/*
	 * Clear GIF and turn on IF for guest (v_intr_masking),
	 * to allow vmexits by external interrupts.
	 */
	vmload	%rax
	sti
	vmrun	%rax
	cli
	vmsave	%rax
	/* NMI may happen here */
	/* guest %rsp saved in vmcb; kernel stack pointer unchanged */
	SAVE_C_REGS
	/* r10-11 are temporary registers */
	movq	VMCB_EXITCODE(%rax), %r10
	cmpq	$VMCB_EXIT_VMMCALL, %r10
	je	handle_syscall
	cmpq	$VMCB_EXIT_INTR, %r10
	je	handle_intr
	/* slow path */
	SAVE_EXTRA_REGS
	SAVE_FPU_REGS
	movq	%rax, %rdi
	movq	%rsp, %rsi
	call	svm_dispatch
	jmp	svm_loop

handle_syscall:
	/* bump %rip to skip vmmcall */
	addq	$3, VMCB_RIP(%rax)
	/* load the syscall number */
	movq	VMCB_RAX(%rax), %rax
	/* invoke the syscall */
	INVOKE_SYSCALL
	/* copy the return value */
	movq	%rax, %r10
	/* restore the vmcb */
	LOAD_RAX_REG
	/* save the return value into vmcb */
	movq	%r10, VMCB_RAX(%rax)
	jmp	svm_fast_path

handle_intr:
	/* don't change %rip */

	stgi
	/*
	 * find out the vector by triggering the interrupt;
	 * need one nop to pass the interrupt shadow
	 */
	sti
	/* vector using the kernel IDT */
	nop
	cli
	clgi
	/* restore the vmcb */
	LOAD_RAX_REG
	/* don't change %rip */
	jmp	svm_fast_path
