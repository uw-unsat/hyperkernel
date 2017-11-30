#include "cpuid.h"
#include "hvm.h"

void svm_init(void);
void vmx_init(void);

void (*hvm_user_init)(void *hvm, register_t rip);
void (*hvm_switch)(void *hvm, void *stack, register_t cr3, timer_t timer, int launched);
void (*hvm_flush)(void *hvm);
void (*hvm_copy)(void *dst, void *src, pid_t pid);
void (*hvm_set_timer)(void *hvm, timer_t timer);
void (*hvm_set_io_bitmap)(void *hvm, void *addr);
void (*hvm_set_pid)(void *hvm, pid_t pid);
void (*hvm_invalidate_tlb)(pid_t pid);

void (*hvm_preempt)(void);
void (*hvm_fault)(void);
int (*hvm_extintr)(uint8_t irq);

void hvm_init(void)
{
    if (cpuid_has(CPUID_FEATURE_SVM))
        return svm_init();

    if (cpuid_has(CPUID_FEATURE_VMX))
        return vmx_init();

    panic("hvm: no svm/vmx");
}
