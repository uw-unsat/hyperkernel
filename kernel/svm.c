#include <uapi/machine/cpufunc.h>
#include <uapi/machine/segment.h>
#include <uapi/machine/trap.h>
#include <machine/memlayout.h>
#include <string.h>
#include "cpuid.h"
#include "hvm.h"
#include "svm.h"

static uint8_t hsave[PAGE_SIZE] __aligned(PAGE_SIZE);
/*
 * I/O & MSR permissions map:
 *
 * We need to intercept all I/O ports and MSRs, so just define
 * a large enough bitmap (with all 1s):
 * - I/O ports: 3 pages;
 * - MSRs: 2 pages.
 */
static uint8_t pm[PAGE_SIZE][3] __aligned(PAGE_SIZE);

/* concatenation of bits 23:20 and 15:8 */
static uint16_t vmcb_seg_attrib(uint64_t desc)
{
    return ((desc >> 44) & 0xf00) | ((desc >> 40) & 0xff);
}

static void svm_user_init(void *ptr, register_t rip)
{
    struct vmcb *vmcb = ptr;
    struct vmcb_ctrl *ctrl;
    struct vmcb_state *state;

    bzero(vmcb, SZ_4K);

    state = &vmcb->state;
    state->efer = rdmsr(MSR_EFER);
    state->cr0 = rcr0();
    state->cr4 = rcr4();
    state->cs.attrib = vmcb_seg_attrib(KERNEL_CS_DESC);
    state->ds.attrib = vmcb_seg_attrib(KERNEL_DS_DESC);
    state->ss.attrib = vmcb_seg_attrib(KERNEL_DS_DESC);
    state->es.attrib = vmcb_seg_attrib(KERNEL_DS_DESC);

    state->rip = rip;
    state->rflags = BIT64(1);
#if 0
	state->cs.selector = GDT_CS;
	state->cs.limit = 0xffffffff;

	state->ds.selector = GDT_DS;
	state->ds.limit = 0xffffffff;

	state->es.selector = GDT_DS;
	state->es.limit = 0xffffffff;

	state->ss.selector = GDT_DS;
	state->ss.limit = 0xffffffff;
#endif

    /* load syscall MSRs */
    state->star = rdmsr(MSR_STAR);
    state->lstar = rdmsr(MSR_LSTAR);
    state->sfmask = rdmsr(MSR_SFMASK);

    ctrl = &vmcb->ctrl;
    ctrl->intercept[VMCB_CR_INTCPT] = VMCB_INTCPT_CR3_WRITE;
    /* intercept external interrupts */
    ctrl->intercept[VMCB_CTRL1_INTCPT] = VMCB_INTCPT_INTR | VMCB_INTCPT_IO | VMCB_INTCPT_MSR;
    ctrl->v_intr_masking = 1;
    ctrl->intercept[VMCB_CTRL2_INTCPT] = VMCB_INTCPT_VMRUN | VMCB_INTCPT_VMMCALL | VMCB_INTCPT_XSETBV;

    /* intercept I/O port & MSR instructions */
    memset(pm, 0xff, sizeof(pm));
    ctrl->iopm_base_pa = kva2pa(pm);
    ctrl->msrpm_base_pa = kva2pa(pm);

    ctrl->asid = 1;

    /* no tlb caching */
    ctrl->tlb_ctrl = VMCB_TLB_FLUSH_ALL;

    /* no vmcb caching */
    ctrl->vmcb_clean = VMCB_CACHE_NONE;
}

/* ignore timer/launched */
static void svm_switch(void *arg, void *stack, register_t cr3, timer_t timer, int launched)
{
    struct vmcb *vmcb = arg;
    struct trap_regs *regs = stack - sizeof(struct trap_regs) - sizeof(struct xsave_area);

    assert((uintptr_t)vmcb % PAGE_SIZE == 0, "vmcb must be page-aligned");

    vmcb->state.cr3 = cr3;

    /* save rax into vmcb */
    vmcb->state.rax = regs->rax;
    /* svm_loop will load this */
    regs->rax = (register_t)vmcb;
    /* reset the kernel stack pointer before starting user space */
    asm volatile("movq %0, %%rsp; jmp svm_loop" : : "r"(regs) : "memory", "cc");
    __builtin_unreachable();
}

static void svm_flush(void *vmcs)
{
    /* do nothing */
}

static void svm_copy(void *dst, void *src, pid_t pid)
{
    struct vmcb *vmcb = dst;
    struct vmcb_ctrl *ctrl = &vmcb->ctrl;

    /* reset io bitmap */
    ctrl->iopm_base_pa = kva2pa(pm);
}

void svm_dispatch(struct vmcb *vmcb, struct trap_regs *regs)
{
    struct vmcb_ctrl *ctrl = &vmcb->ctrl;
    struct vmcb_state *state = &vmcb->state;

    pr_info("svm: vmexit rip=%" PRIx64 ", exitcode=%lx %lx %lx %lx\n", state->rip,
            ctrl->exitcode, ctrl->exitinfo1, ctrl->exitinfo2, ctrl->exitintinfo);

    /* We could inject back #GP but it's not useful; just kill the process. */
    switch (ctrl->exitcode) {
    default:
        break;
    case VMCB_EXIT_IO:
        pr_info("svm: vmexit port=0x%x\n", (uint16_t)(ctrl->exitinfo1 >> 16));
        break;
    }

    if (hvm_fault)
        hvm_fault();
    panic(NULL);
}

static void svm_set_timer(void *vmcb, timer_t timer)
{
    /* svm has no preemption timer like vmx */
    return;
}

static void svm_set_io_bitmap(void *hvm, void *addr)
{
    struct vmcb *vmcb = hvm;
    struct vmcb_ctrl *ctrl = &vmcb->ctrl;

    assert(ctrl->iopm_base_pa == kva2pa(pm), "io bitmap already in use");
    ctrl->iopm_base_pa = kva2pa(addr);
}

static void svm_set_pid(void *hvm, pid_t pid)
{
}

static void svm_invalidate_tlb(pid_t pid)
{
}

void svm_init(void)
{
    uint64_t msr;

    msr = rdmsr(MSR_VM_CR);
    if (msr & VM_CR_SVMDIS)
        panic("svm disabled");

    /* set EFER.SVME */
    wrmsr(MSR_EFER, rdmsr(MSR_EFER) | EFER_SVME);
    pr_info("svm: enabled\n");

    /* set the host save area */
    wrmsr(MSR_VM_HSAVE_PA, kva2pa(hsave));

    /* clear GIF */
    clgi();

    hvm_user_init = svm_user_init;
    hvm_switch = svm_switch;
    hvm_flush = svm_flush;
    hvm_copy = svm_copy;
    hvm_set_timer = svm_set_timer;
    hvm_set_io_bitmap = svm_set_io_bitmap;
    hvm_invalidate_tlb = svm_invalidate_tlb;
    hvm_set_pid = svm_set_pid;
}
