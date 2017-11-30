#include <uapi/machine/trap_support.h>
#include <uapi/errno.h>
#include "linux.h"
#include "syscall.h"

#define SYSCALL(sym)						\
	.global	sys_##sym;					\
	sys_##sym:						\
		movq	$SYS_##sym, %rax;			\
		vmcall;						\
		ret

SYSCALL(map_page_desc)
SYSCALL(map_pml4)
SYSCALL(map_proc)
SYSCALL(map_dev)
SYSCALL(map_file)
SYSCALL(alloc_pdpt)
SYSCALL(alloc_pd)
SYSCALL(alloc_pt)
SYSCALL(alloc_frame)
SYSCALL(copy_frame)
SYSCALL(protect_frame)
SYSCALL(free_pdpt)
SYSCALL(free_pd)
SYSCALL(free_pt)
SYSCALL(free_frame)
SYSCALL(reclaim_page)
SYSCALL(set_proc_name)
SYSCALL(set_runnable)
SYSCALL(switch)
SYSCALL(kill)
SYSCALL(reap)
SYSCALL(reparent)
SYSCALL(send)
SYSCALL(recv)
SYSCALL(reply_wait)
SYSCALL(call)
SYSCALL(create)
SYSCALL(close)
SYSCALL(dup)
SYSCALL(dup2)
SYSCALL(lseek)
SYSCALL(map_pcipage)
SYSCALL(alloc_iommu_root)
SYSCALL(alloc_iommu_pdpt)
SYSCALL(alloc_iommu_pd)
SYSCALL(alloc_iommu_pt)
SYSCALL(alloc_iommu_frame)
SYSCALL(map_iommu_frame)
SYSCALL(reclaim_iommu_frame)
SYSCALL(reclaim_iommu_root)
SYSCALL(alloc_vector)
SYSCALL(reclaim_vector)
SYSCALL(alloc_intremap)
SYSCALL(reclaim_intremap)
SYSCALL(ack_intr)
SYSCALL(alloc_io_bitmap)
SYSCALL(alloc_port)
SYSCALL(reclaim_port)
SYSCALL(debug_exit)
SYSCALL(debug_print_console)
SYSCALL(debug_print_screen)
SYSCALL(debug_dmesg)
SYSCALL(debug_sysctl)

.global	exec
exec:
	/* push rbp to align the stack; also good for stacktrace */
	push	%rbp
	movq	%rsp, %rbp
	/* switch to high stack */
	movq	$ulib_stack_top, %rsp
	/* %rbp is preserved across call */
	call	do_exec
	/* switch back the stack on error */
	movq	%rbp, %rsp
	pop	%rbp
	ret

.global fexec
fexec:
	movq	$ulib_stack_top, %rsp
	/* do_fexec doesn't return */
	jmp	do_fexec

.global linux_syscall_entry
linux_syscall_entry:
	/* save syscall return address (to fake a regular return) */
	push	%rcx
	/* save rflags to stack (to pop later) */
	push	%r11
	/* validate the syscall number */
	cmpq	$NR_linux_syscalls, %rax
	jb	1f
	movq	$-ENOSYS, %rax
	/* need to restore rflags */
	jmp	2f
1:
	subq	$TRAP_REGS_SIZE, %rsp
	SAVE_C_REGS_EXCEPT_RAX
	/* sync syscall calling convention with C's */
	movq	%r10, %rcx
	movq	$linux_syscalls, %r10
	leaq	(%r10, %rax, 8), %rax
	call	*(%rax)
	LOAD_C_REGS_EXCEPT_RAX
	addq	$TRAP_REGS_SIZE, %rsp
2:
	popfq
	retq
