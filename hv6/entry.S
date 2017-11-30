#include <uapi/machine/trap_support.h>
#include "config.h"

/*
 * Don't return from functions in this file.  Instead, call run_current.
 *
 * Upon entry the rax field in struct trap_reg may be the vmcs;
 * once we change it, we cannot simply return.
 *
 * Flush hvm state from cpu state to memory before each call.  This is
 * necessary for context switching.
 */

.macro	SYS_WRAP	proc
	/* save all GP registers (except %rax) */
	SAVE_EXTRA_REGS	offset=8
	SAVE_FPU_REGS offset=8
	/* set default return value to 0 */
	movq	$0, TRAP_REGS_RAX+8(%rsp)
	/* align the stack */
	push	%rbp
	movq	%rsp, %rbp
	/* restore parameters */
	LOAD_C_REGS offset=16
	call	\proc
	pop	%rbp
	/* set the return value */
	movq	%rax, TRAP_REGS_RAX+8(%rsp)
	jmp	run_current
.endm

.global	sys_clone
sys_clone:
  SYS_WRAP clone_proc

.global	sys_switch
sys_switch:
	SYS_WRAP sys_switch_helper

.global	sys_send
sys_send:
	SYS_WRAP send_proc

.global	sys_recv
sys_recv:
	SYS_WRAP recv_proc

.global	sys_call
sys_call:
	SYS_WRAP call_proc

.global	sys_reply_wait
sys_reply_wait:
	SYS_WRAP reply_wait_proc
