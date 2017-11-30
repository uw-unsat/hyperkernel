#include <uapi/machine/cpufunc.h>
#include <uapi/machine/mmu.h>
#include <uapi/machine/segment.h>
#include <uapi/machine/trap.h>

#define GDT_ENTRY_CS 1
#define GDT_ENTRY_DS 2
#define GDT_ENTRY_TSS 3
#define GDT_CS (GDT_ENTRY_CS << 3)
#define GDT_DS (GDT_ENTRY_DS << 3)
#define GDT_TSS (GDT_ENTRY_TSS << 3)

static struct tss tss = {
    .rsp0 = 0, /* no stack switch */
};

static uint64_t gdt[] = {
    0, KERNEL_CS_DESC, KERNEL_DS_DESC, 0, 0, /* TSS */
};

static struct pseudo_desc gdt_desc = {
    sizeof(gdt) - 1, (uint64_t)gdt,
};

static struct gate_desc idt[256] = {{0}};

static struct pseudo_desc idt_desc = {
    sizeof(idt) - 1, (uint64_t)idt,
};

void trap_init(void)
{
    uint64_t tss_addr = (uint64_t)&tss;
    size_t i;
    extern void *trap_vectors[];

    gdt[GDT_ENTRY_TSS] =
        SEG_TSSA | SEG_P | SEG_A | SEG_BASELO(tss_addr) | SEG_LIMIT(sizeof(tss) - 1);
    gdt[GDT_ENTRY_TSS + 1] = SEG_BASEHI(tss_addr);

    for (i = 0; i < countof(idt); ++i)
        set_gate_desc(&idt[i], 0, GDT_CS, trap_vectors[i], KERNEL_PL);
    lgdt(&gdt_desc);

    asm volatile("mov	$16, %%ax\n"
                 "mov	%%ax, %%ds\n"
                 "mov	%%ax, %%es\n"
                 "mov	%%ax, %%ss\n"
                 "mov	$8, %%rax\n"
                 "pushq	%%rax\n"
                 "pushq	$1f\n"
                 "lretq\n"
                 "1:\n"
                 "nop"
                 :
                 :
                 : "rax");

    ltr(GDT_TSS);
    lidt(&idt_desc);
}
