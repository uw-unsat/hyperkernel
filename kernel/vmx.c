#include <uapi/machine/cpufunc.h>
#include <uapi/machine/segment.h>
#include <uapi/machine/trap.h>
#include <machine/memlayout.h>
#include <string.h>
#include <xapic.h>
#include "cpuid.h"
#include "hvm.h"
#include "types.h"
#include "proc.h"
#include "vmx.h"

static uint32_t pinbased_ones_mask = PINBASED_EXTINT_EXITING
#if ENABLED(CONFIG_PREEMPT)
                                   | PINBASED_PREMPTION_TIMER
#endif
                                   ;
static uint32_t pinbased_zeros_mask = 0;
static uint32_t procbased_ones_mask = PROCBASED_INVLPG_EXITING
                                    | PROCBASED_CR8_STORE_EXITING
                                    | PROCBASED_CR8_LOAD_EXITING
                                    | PROCBASED_MOV_DR_EXITING
                                    | PROCBASED_CR3_LOAD_EXITING
                                    | PROCBASED_IO_EXITING
                                    | PROCBASED_SECONDARY_CONTROLS;
static uint32_t procbased_zeros_mask = PROCBASED_RDTSC_EXITING
                                     | PROCBASED_CR3_STORE_EXITING
                                     | PROCBASED_IO_BITMAPS;
static uint32_t procbased2_ones_mask = PROCBASED2_ENABLE_RDTSCP
                                     | PROCBASED2_WBINVD_EXITING
#if ENABLED(CONFIG_VPID)
                                     | PROCBASED2_ENABLE_VPID
#endif
                                     ;
static uint32_t procbased2_zeros_mask = 0;
static uint32_t exit_ones_mask = VM_EXIT_HOST_LMA
                                 | VM_EXIT_ACKNOWLEDGE_INTERRUPT
#if ENABLED(CONFIG_PREEMPT)
                                 | VM_EXIT_SAVE_PREEMPTION_TIMER
#endif
                                 ;
static uint32_t exit_zeros_mask = 0;
static uint32_t entry_ones_mask = 0 | VM_ENTRY_GUEST_LMA;
static uint32_t entry_zeros_mask = 0;

static uint32_t revision_id;
static uint32_t pinbased_ctls;
static uint32_t procbased_ctls;
static uint32_t procbased_ctls2;
static uint32_t exit_ctls;
static uint32_t entry_ctls;

static uint16_t vmx_timer_resolution;

static uint8_t vmxon_region[PAGE_SIZE] __aligned(PAGE_SIZE);

static struct vmcs *current_vmcs;

extern void vmx_entry(void);

/* check bits in MSR_IA32_FEATURE_CONTROL */
static void check_feature_control(void)
{
    uint64_t bits, mask;

    bits = rdmsr(MSR_IA32_FEATURE_CONTROL);
    mask = FEATURE_CONTROL_LOCK | FEATURE_CONTROL_ENABLE_VMXON_OUTSIDE_SMX;

    if (!(bits & FEATURE_CONTROL_LOCK)) {
        /* must set the lock bit before vmxon */
        wrmsr(MSR_IA32_FEATURE_CONTROL, bits | mask);
        bits = rdmsr(MSR_IA32_FEATURE_CONTROL);
    }

    if ((bits & mask) != mask)
        panic("vmx: disabled");
}

/* check bits in MSR_IA32_VMX_EPT_VPID_CAP */
static void check_vpid_cap(void)
{
    uint64_t vpid_cap;

    vpid_cap = rdmsr(MSR_IA32_VMX_EPT_VPID_CAP);
    /* check vpid-related bits */
    if (!(vpid_cap & VMX_INVVPID_SUPPORTED))
        panic("vmx: no invvpid");
    if (!(vpid_cap & VMX_INVVPID_SINGLE_CONTEXT_SUPPORTED))
        panic("vmx: no single-context invvpid");
}

/* use algorithm 3 to determine capabilities */
static uint32_t vmx_capabilities(uint64_t basic, uint32_t msr, uint32_t true_msr,
                                 uint32_t ones_mask, uint32_t zeros_mask)
{
    uint64_t bits, true_bits;
    uint32_t cap = 0;
    int i;

    assert((ones_mask ^ zeros_mask) == (ones_mask | zeros_mask), "invalid masks - either 0 or 1");

    bits = rdmsr(msr);
    if (basic & VMX_BASIC_TRUE_CTLS)
        true_bits = rdmsr(true_msr);
    else
        true_bits = bits;

    for (i = 0; i < 32; ++i) {
        bool allowed_0, allowed_1;

        allowed_0 = !(true_bits & BIT64(i));
        allowed_1 = true_bits & BIT64(i + 32);
        assert(allowed_0 || allowed_1, "must be either 0- or 1-allowed");

        /* default0 */
        if (allowed_0 && !allowed_1) {
            if (ones_mask & BIT32(i))
                panic("bit %d is not allowed to be 1", i);
            continue;
        }

        /* default1 */
        if (!allowed_0 && allowed_1) {
            if (zeros_mask & BIT32(i))
                panic("bit %d is not allowed to be 0", i);
            cap |= BIT32(i);
            continue;
        }

        /* can be either 0 or 1 in true_bits */

        /* known to be 0 */
        if (zeros_mask & BIT32(i))
            continue;

        /* known to be 1 */
        if (ones_mask & BIT32(i)) {
            cap |= BIT32(i);
            continue;
        }

        /* unknown, can be 0 in bits */
        if (!(bits & BIT64(i)))
            continue;

        /* unknown, must be 1 in bits */
        if (bits & BIT64(i + 32)) {
            cap |= BIT32(i);
            continue;
        }

        panic("unable to set bit %d", i);
    }

    return cap;
}

/*
 * 15:0  - bits 23:8 of the upper 32 bits of a 64-bit segment descriptor
 * 16    - unusable
 * 31:17 - reserved
 */
static uint32_t vmcb_seg_attrib(uint64_t desc)
{
    return desc >> 40;
}

static void vmx_user_init(void *ptr, register_t rip)
{
    struct vmcs *vmcs = ptr;

    vmclear(kva2pa(vmcs));

    /* set the revision id: must be done before vmptrld */
    vmcs->revision_id = revision_id;

    /* load vmcs */
    vmptrld(kva2pa(vmcs));

    /* set control fields */
    vmwrite(VMCS_PINBASED_CTLS, pinbased_ctls);
    vmwrite(VMCS_PRI_PROCBASED_CTLS, procbased_ctls);
    vmwrite(VMCS_SEC_PROCBASED_CTLS, procbased_ctls2);
    vmwrite(VMCS_EXIT_CTLS, exit_ctls);
    vmwrite(VMCS_ENTRY_CTLS, entry_ctls);

    vmwrite(VMCS_LINK_POINTER, ~UINT64_C(0));

    /* set guest-state fields */
    vmwrite(VMCS_GUEST_CR0, rcr0());
    // CR0_PG | CR0_PE | CR0_WP | CR0_MP | CR0_ET | CR0_NE);
    vmwrite(VMCS_GUEST_CR4, rcr4());
    vmwrite(VMCS_GUEST_IA32_EFER, rdmsr(MSR_EFER));
    vmwrite(VMCS_GUEST_RFLAGS, 0x2); // FIXME
    vmwrite(VMCS_GUEST_RIP, rip);

    vmwrite(VMCS_GUEST_CS_AR_BYTES, vmcb_seg_attrib(KERNEL_CS_DESC));
    vmwrite(VMCS_GUEST_DS_AR_BYTES, vmcb_seg_attrib(KERNEL_DS_DESC));
    vmwrite(VMCS_GUEST_ES_AR_BYTES, vmcb_seg_attrib(KERNEL_DS_DESC));
    vmwrite(VMCS_GUEST_SS_AR_BYTES, vmcb_seg_attrib(KERNEL_DS_DESC));
    vmwrite(VMCS_GUEST_FS_AR_BYTES, vmcb_seg_attrib(KERNEL_DS_DESC));
    vmwrite(VMCS_GUEST_GS_AR_BYTES, vmcb_seg_attrib(KERNEL_DS_DESC));

    vmwrite(VMCS_GUEST_CS_LIMIT, 0xffffffff);
    vmwrite(VMCS_GUEST_DS_LIMIT, 0xffffffff);
    vmwrite(VMCS_GUEST_ES_LIMIT, 0xffffffff);
    vmwrite(VMCS_GUEST_SS_LIMIT, 0xffffffff);
    vmwrite(VMCS_GUEST_FS_LIMIT, 0xffffffff);
    vmwrite(VMCS_GUEST_GS_LIMIT, 0xffffffff);

    vmwrite(VMCS_GUEST_LDTR_SELECTOR, 0);
    vmwrite(VMCS_GUEST_LDTR_AR_BYTES, 0x0082);
    vmwrite(VMCS_GUEST_LDTR_BASE, 0);
    vmwrite(VMCS_GUEST_LDTR_LIMIT, 0);

    vmwrite(VMCS_GUEST_TR_AR_BYTES, 0x0080 | 11);
    vmwrite(VMCS_GUEST_TR_LIMIT, 0xff);

    /* set host-state fields */
    vmwrite(VMCS_HOST_CS_SELECTOR, GDT_CS);
    vmwrite(VMCS_HOST_DS_SELECTOR, GDT_DS);
    vmwrite(VMCS_HOST_ES_SELECTOR, GDT_DS);
    vmwrite(VMCS_HOST_SS_SELECTOR, GDT_DS);
    vmwrite(VMCS_HOST_TR_SELECTOR, GDT_TSS);
    // TODO: host fs/gs
    vmwrite(VMCS_HOST_FS_BASE, rdmsr(MSR_IA32_FS_BASE));
    vmwrite(VMCS_HOST_GS_BASE, rdmsr(MSR_IA32_GS_BASE));

    vmwrite(VMCS_HOST_CR0, rcr0());
    vmwrite(VMCS_HOST_CR3, rcr3());
    vmwrite(VMCS_HOST_CR4, rcr4());

    // TODO: tr/gdtr

    vmwrite(VMCS_HOST_RIP, (uintptr_t)vmx_entry);

    if (!current_vmcs)
        current_vmcs = vmcs;
    vmptrld(kva2pa(current_vmcs));
}

static void vmx_switch(void *vmcs, void *stack, register_t cr3, timer_t timer, int launched)
{
    struct trap_regs *regs = stack - sizeof(struct trap_regs) - sizeof(struct xsave_area);

    current_vmcs = vmcs;
    vmptrld(kva2pa(vmcs));

    vmwrite(VMCS_GUEST_CR3, cr3);
#if ENABLED(CONFIG_PREEMPT)
    /* recharge only after preemption */
    if (!vmread(VMCS_PREEMPTION_TIMER_VALUE))
        vmwrite(VMCS_PREEMPTION_TIMER_VALUE, timer >> vmx_timer_resolution);
#endif

    vmwrite(VMCS_HOST_RSP, (uintptr_t)regs);

    asm volatile("cmpl $0, %0; movq %1, %%rsp; je vmx_launch; jmp vmx_resume"
                 :
                 : "r"(launched), "r"(regs)
                 : "memory", "cc");
    __builtin_unreachable();
}

static void vmx_flush(void *vmcs)
{
    /* must call vmlaunch (rather than vmresume) after this */
    vmclear((uint64_t)vmcs);
    current_vmcs = NULL;
}

static void vmx_set_vpid(void *vmcs, pid_t pid)
{
    vpid_t vpid;

    assert(vmcs == current_vmcs, "incorrect current vmcs");
    vpid = pid_vpid(pid);
    vmwrite(VMCS_VPID, vpid);
}

static void vmx_invalidate_tlb(pid_t pid)
{
    vpid_t vpid;

    vpid = pid_vpid(pid);
    invvpid(INVVPID_SINGLE_CONTEXT, 0, vpid);
}

static void vmx_copy(void *dst, void *src, pid_t pid)
{
    vpid_t vpid;

    assert(current_vmcs == NULL, "incorrect current vmcs");

    current_vmcs = dst;
    vmptrld(kva2pa(dst));

    /* reset io bitmap */
    vmwrite(VMCS_PRI_PROCBASED_CTLS, procbased_ctls);
    vmwrite(VMCS_IO_BITMAP_A, 0);
    vmwrite(VMCS_IO_BITMAP_B, 0);

    vpid = pid_vpid(pid);
    vmwrite(VMCS_VPID, vpid);
    invvpid(INVVPID_SINGLE_CONTEXT, 0, vpid);

    /* is this necessary? */
    vmclear(kva2pa(dst));
    current_vmcs = NULL;
}

void vmx_dispatch(struct trap_regs *regs)
{
    uint32_t reason;
    unsigned long qual;

    reason = vmread(VMCS_EXIT_REASON);
    qual = vmread(VMCS_EXIT_QUALIFICATION);

    /* We could inject back #GP but it's not useful; just kill the process. */
    switch (reason) {
    default:
        break;
    case EXIT_REASON_INOUT:
        pr_info("vmx: vmexit port=0x%x\n", (uint16_t)((qual >> 16) & 0xffff));
        break;
#if ENABLED(CONFIG_PREEMPT)
    case EXIT_REASON_VMX_PREEMPT:
        /* may not return */
        if (hvm_preempt)
            hvm_preempt();
        break;
#endif
    }

    pr_info("vmx: vmexit reason=%u qualification=%lx\n", reason, qual);

    if (hvm_fault)
        hvm_fault();
    panic(NULL);
}

void vmx_extintr(void)
{
    uint32_t info;

    info = vmread(VMCS_EXIT_INTR_INFO);
    if (!(info & VMCS_INTR_VALID))
        return;
    switch (info & VMCS_INTR_T_MASK) {
    default:
        pr_info("vmx_extintr: %x\n", info);
        break;
    case VMCS_INTR_T_HWINTR:
        if (hvm_extintr)
            hvm_extintr(info & VMCS_INTR_V_MASK);
        xapic_eoi();
        break;
    }
}

static void print_controls(const char *prefix, uint32_t ctl)
{
    uint32_t i;

    pr_info("vmx: %s\nvmx:  ", prefix);
    for (i = 0; i < 32; ++i) {
        if (ctl & BIT32(i))
            pr_info(" %d", i);
    }
    pr_info("\n");
}

static void vmx_set_timer(void *vmcs, timer_t timer)
{
    assert(vmcs == current_vmcs, "incorrect current vmcs");
#if ENABLED(CONFIG_PREEMPT)
    vmwrite(VMCS_PREEMPTION_TIMER_VALUE, timer / (1 << vmx_timer_resolution));
#endif
}

static void vmx_set_io_bitmap(void *vmcs, void *addr)
{
    uint32_t this_procbased_ctls;

    assert(vmcs == current_vmcs, "incorrect current vmcs");

    this_procbased_ctls = vmread(VMCS_PRI_PROCBASED_CTLS);
    assert(!(this_procbased_ctls & PROCBASED_IO_BITMAPS), "io bitmap already in use");
    this_procbased_ctls |= PROCBASED_IO_BITMAPS;
    vmwrite(VMCS_PRI_PROCBASED_CTLS, this_procbased_ctls);

    /* assume at last 8K from addr */
    vmwrite(VMCS_IO_BITMAP_A, kva2pa(addr));
    vmwrite(VMCS_IO_BITMAP_B, kva2pa(addr + PAGE_SIZE));
}

void vmx_init(void)
{
    uint64_t basic, cr0, cr4;

    check_feature_control();

    check_vpid_cap();

    basic = rdmsr(MSR_IA32_VMX_BASIC);
    revision_id = bit_get_field(basic, VMX_BASIC_REVISION_ID);

    pinbased_ctls =
        vmx_capabilities(basic, MSR_IA32_VMX_PINBASED_CTLS, MSR_IA32_VMX_TRUE_PINBASED_CTLS,
                         pinbased_ones_mask, pinbased_zeros_mask);

    procbased_ctls =
        vmx_capabilities(basic, MSR_IA32_VMX_PROCBASED_CTLS, MSR_IA32_VMX_TRUE_PROCBASED_CTLS,
                         procbased_ones_mask, procbased_zeros_mask);

    procbased_ctls2 =
        vmx_capabilities(basic, MSR_IA32_VMX_PROCBASED_CTLS2, MSR_IA32_VMX_PROCBASED_CTLS2,
                         procbased2_ones_mask, procbased2_zeros_mask);

    exit_ctls = vmx_capabilities(basic, MSR_IA32_VMX_EXIT_CTLS, MSR_IA32_VMX_EXIT_CTLS,
                                 exit_ones_mask, exit_zeros_mask);

    entry_ctls = vmx_capabilities(basic, MSR_IA32_VMX_ENTRY_CTLS, MSR_IA32_VMX_ENTRY_CTLS,
                                  entry_ones_mask, entry_zeros_mask);

    print_controls("pin-based VM-execution controls", pinbased_ctls);
    print_controls("primary processor-based VM-execution controls", procbased_ctls);
    print_controls("secondary processor-based VM-execution controls", procbased_ctls2);
    print_controls("VM-exit controls", exit_ctls);
    print_controls("VM-entry controls", entry_ctls);

    /* CR0 */
    cr0 = rcr0();
    cr0 &= rdmsr(MSR_IA32_VMX_CR0_FIXED1);
    cr0 |= rdmsr(MSR_IA32_VMX_CR0_FIXED0);
    lcr0(cr0);

    /* CR4 */
    cr4 = rcr4();
    cr4 &= rdmsr(MSR_IA32_VMX_CR4_FIXED1);
    cr4 |= rdmsr(MSR_IA32_VMX_CR4_FIXED0);
    cr4 |= CR4_VMXE;
    lcr4(cr4);

    /* initialize the VMXON region */
    memcpy(vmxon_region, &revision_id, sizeof(revision_id));
    vmxon(kva2pa(vmxon_region));
    pr_info("vmx: vmxon enabled\n");

    /* Timer resolution */
    vmx_timer_resolution = rdmsr(MSR_IA32_VMX_MISC) & VMX_MISC_TIMER_RESOLUTION;
    pr_info("vmx: preemption timer resolution: %d\n", vmx_timer_resolution);

    hvm_user_init = vmx_user_init;
    hvm_switch = vmx_switch;
    hvm_flush = vmx_flush;
    hvm_copy = vmx_copy;
    hvm_set_timer = vmx_set_timer;
    hvm_invalidate_tlb = vmx_invalidate_tlb;
    hvm_set_io_bitmap = vmx_set_io_bitmap;
    hvm_set_pid = vmx_set_vpid;
}
