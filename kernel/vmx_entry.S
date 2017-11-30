#include "hvm_support.S"
#include "vmx.h"

.global	vmx_entry
vmx_entry:
	SAVE_C_REGS_EXCEPT_RAX
	/* use r10-11 as temporary registers */

	movq	$VMCS_EXIT_REASON, %r11
	vmread	%r11, %r10

	cmpq	$EXIT_REASON_VMCALL, %r10
	je	handle_syscall

	cmpq	$EXIT_REASON_CPUID, %r10
	je	handle_cpuid

	cmpq	$EXIT_REASON_EXT_INTR, %r10
	je	handle_ext_intr

	/* slow path */
	SAVE_RAX_REG
	SAVE_EXTRA_REGS
	SAVE_FPU_REGS
	movq	%rsp, %rdi
	/* vmx_dispatch will call vmclear so vmlaunch is okay later */
	callq	vmx_dispatch
	jmp	vmx_resume

.global	vmx_launch
vmx_launch:
	LOAD_FPU_REGS
	LOAD_EXTRA_REGS
	LOAD_C_REGS
	vmlaunch

.global	vmx_resume
vmx_resume:
	LOAD_FPU_REGS
	LOAD_EXTRA_REGS
	LOAD_C_REGS
	vmresume

handle_syscall:
	/* bump rip to skip vmcall */
	movq	$VMCS_GUEST_RIP, %r11
	vmread	%r11, %r10
	addq	$3, %r10
	vmwrite	%r10, %r11
	/* invoke the syscall */
	INVOKE_SYSCALL
	/* %rax holds the return value */
	LOAD_C_REGS_EXCEPT_RAX
	vmresume

/* cpuid causes vmexit unconditionally */
handle_cpuid:
	/* bump %rip to skip cpuid */
	movq	$VMCS_GUEST_RIP, %r11
	vmread	%r11, %r10
	addq	$2, %r10
	vmwrite	%r10, %r11
	/*
	 * input: %rax, %rcx
	 * output: %eax, %ebx, %ecx, %edx
	 */
	cpuid
	LOAD_C_REGS_EXCEPT_RAX_RCX_RDX
	vmresume

handle_ext_intr:
	/* don't change %rip */
	SAVE_RAX_REG
	callq	vmx_extintr
	LOAD_C_REGS
	vmresume
