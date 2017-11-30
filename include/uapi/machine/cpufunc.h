#pragma once

#include <uapi/machine/msr.h>

#define reg_read(r)                                                                                \
    ({                                                                                             \
        uint64_t val;                                                                              \
        asm volatile("movq %%" #r ", %0" : "=r"(val));                                             \
        val;                                                                                       \
    })

#define reg_write(r, val) ({ asm volatile("movq %0, %%" #r : : "r"(val)); })

static inline void cpuid(uint32_t leaf, uint32_t *regs)
{
    asm volatile("cpuid" : "=a"(regs[0]), "=b"(regs[1]), "=c"(regs[2]), "=d"(regs[3]) : "a"(leaf));
}

static inline void cpuid2(uint32_t leaf, uint32_t subleaf, uint32_t *regs)
{
    asm volatile("cpuid"
                 : "=a"(regs[0]), "=b"(regs[1]), "=c"(regs[2]), "=d"(regs[3])
                 : "a"(leaf), "c"(subleaf));
}

static inline uint8_t inb(uint16_t port)
{
    uint8_t data;

    asm volatile("inb %w1, %0" : "=a"(data) : "Nd"(port));
    return data;
}

static inline uint16_t inw(uint16_t port)
{
    uint16_t data;

    asm volatile("inw %w1, %0" : "=a"(data) : "Nd"(port));
    return data;
}

static inline uint32_t inl(uint16_t port)
{
    uint32_t data;

    asm volatile("inl %w1, %0" : "=a"(data) : "Nd"(port));
    return data;
}

static inline void outb(uint16_t port, uint8_t data)
{
    asm volatile("outb %0, %w1" : : "a"(data), "Nd"(port));
}

static inline void outsb(uint16_t port, const void *addr, size_t count)
{
    asm volatile("cld; rep; outsb"
                 : "+S"(addr), "+c"(count)
                 : "d"(port));
}

static inline void outw(uint16_t port, uint16_t data)
{
    asm volatile("outw %0, %w1" : : "a"(data), "Nd"(port));
}

static inline void outl(uint16_t port, uint32_t data)
{
    asm volatile("outl %0, %w1" : : "a"(data), "Nd"(port));
}

static inline void lcr0(uint64_t val)
{
    reg_write(cr0, val);
}

static inline uint64_t rcr0(void)
{
    return reg_read(cr0);
}

static inline uint64_t rcr2(void)
{
    return reg_read(cr2);
}

static inline void lcr3(uint64_t val)
{
    reg_write(cr3, val);
}

static inline uint64_t rcr3(void)
{
    return reg_read(cr3);
}

static inline void lcr4(uint64_t val)
{
    reg_write(cr4, val);
}

static inline uint64_t rcr4(void)
{
    return reg_read(cr4);
}

static inline void invlpg(const void *addr)
{
    asm volatile("invlpg (%0)" : : "r"(addr) : "memory");
}

static inline void lgdt(void *addr)
{
    asm volatile("lgdt (%0)" : : "r"(addr) : "memory");
}

static inline void lidt(void *addr)
{
    asm volatile("lidt (%0)" : : "r"(addr) : "memory");
}

static inline void lldt(uint16_t sel)
{
    asm volatile("lldt %0" : : "r"(sel) : "memory");
}

static inline void ltr(uint16_t sel)
{
    asm volatile("ltr %0" : : "r"(sel) : "memory");
}

static inline void lfs(uint16_t sel)
{
    asm volatile("mov  %%ax, %%fs" : : "a"(sel) : "memory");
}

static inline void lgs(uint16_t sel)
{
    asm volatile("mov  %%ax, %%gs" : : "a"(sel) : "memory");
}

static inline void pause(void)
{
    asm volatile("pause");
}

static inline void halt(void)
{
    asm volatile("hlt");
}

static inline uint64_t read_rflags(void)
{
    uint64_t rflags;

    asm volatile("pushfq; popq %0" : "=r"(rflags));
    return rflags;
}

static inline void write_rflags(uint64_t rflags)
{
    asm volatile("pushq %0; popfq" : : "r"(rflags));
}

static inline void cli(void)
{
    asm volatile("cli" : : : "memory");
}

static inline void sti(void)
{
    asm volatile("sti" : : : "memory");
}

static inline uint64_t rdmsr(uint32_t msr)
{
    uint32_t lo, hi;

    asm volatile("rdmsr" : "=a"(lo), "=d"(hi) : "c"(msr));
    return lo | ((uint64_t)hi << 32);
}

static inline void wrmsr(uint32_t msr, uint64_t val)
{
    uint32_t lo = val & 0xffffffff, hi = val >> 32;

    asm volatile("wrmsr" : : "c"(msr), "a"(lo), "d"(hi) : "memory");
}

static inline uint64_t rdtsc(void)
{
    uint32_t lo, hi;

    asm volatile("rdtsc" : "=a"(lo), "=d"(hi));
    return lo | ((uint64_t)hi << 32);
}

static inline uint64_t rdtscp(uint32_t *auxp)
{
    uint32_t lo, hi, aux;

    asm volatile("rdtscp" : "=a"(lo), "=d"(hi), "=c"(aux));
    if (auxp)
        *auxp = aux;
    return lo | ((uint64_t)hi << 32);
}

static inline uint64_t rdrsp(void)
{
    uint64_t rsp;
    asm volatile("mov %%rsp, %0" : "=r"(rsp));
    return rsp;
}

static inline uint8_t mmio_read8(void *addr)
{
    volatile uint8_t *p = addr;

    return *p;
}

static inline void mmio_write8(void *addr, uint8_t val)
{
    volatile uint8_t *p = addr;

    *p = val;
}


static inline uint16_t mmio_read16(void *addr)
{
    volatile uint16_t *p = addr;

    return *p;
}

static inline void mmio_write16(void *addr, uint16_t val)
{
    volatile uint16_t *p = addr;

    *p = val;
}

static inline uint32_t mmio_read32(void *addr)
{
    volatile uint32_t *p = addr;

    return *p;
}

static inline void mmio_write32(void *addr, uint32_t val)
{
    volatile uint32_t *p = addr;

    *p = val;
}

static inline uint64_t mmio_read64(void *addr)
{
    volatile uint64_t *p = addr;

    return *p;
}

static inline void mmio_write64(void *addr, uint64_t val)
{
    volatile uint64_t *p = addr;

    *p = val;
}

/* vmx instructions */

static inline void vmxon(uint64_t addr)
{
    asm volatile("vmxon %0; 1: jbe 1b" : : "m"(addr) : "memory");
}

static inline void vmclear(uint64_t addr)
{
    asm volatile("vmclear %0; 1: jbe 1b" : : "m"(addr) : "memory");
}

static inline void vmptrld(uint64_t addr)
{
    asm volatile("vmptrld %0; 1: jbe 1b" : : "m"(addr) : "memory");
}

static inline void vmptrst(uint64_t *addr)
{
    asm volatile("vmptrst %[addr]" : : [addr] "m"(*addr) : "memory");
}

static inline uint64_t vmread(uint64_t field)
{
    uint64_t value;

    asm volatile("vmread %1, %0; 1: jbe 1b" : "=rm"(value) : "r"(field));
    return value;
}

static inline void vmwrite(uint64_t field, uint64_t value)
{
    asm volatile("vmwrite %1, %0; 1: jbe 1b" : : "r"(field), "rm"(value) : "memory");
}

static inline noreturn void vmlaunch(void)
{
    asm volatile("vmlaunch");
    __builtin_unreachable();
}

/* svm instructions */
static inline void vmsave(void *addr)
{
    asm volatile("vmsave %0" : : "a"(addr) : "memory", "cc");
}

static inline void clgi(void)
{
    asm volatile ("clgi");
}

static inline void xsetbv(uint32_t reg, uint64_t val)
{
    uint32_t lo, hi;

    lo = val;
    hi = val >> 32;
    asm volatile("xsetbv" : : "c"(reg), "a"(lo), "d"(hi));
}

static inline int is_kvm(void)
{
    uint32_t regs[4] = { 0 };

    cpuid(0x40000000, regs);
    return regs[1] == 0x4b4d564b && regs[2] == 0x564b4d56 && regs[3] == 0x4d;
}
