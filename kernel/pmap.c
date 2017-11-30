#include <uapi/machine/cpufunc.h>
#include <uapi/machine/mmu.h>
#include <machine/memlayout.h>
#include <bootmem.h>
#include <multiboot.h>
#include <string.h>
#include <symtable.h>

static const char *e820_type(uint32_t type)
{
    static const char *const e820_types[] = {
            [E820_RAM] = "RAM",           [E820_RESERVED] = "reserved",
            [E820_ACPI] = "ACPI tables",  [E820_NVS] = "ACPI non-volatile storage",
            [E820_UNUSABLE] = "unusable",
    };

    if (type >= countof(e820_types) || !e820_types[type])
        type = E820_UNUSABLE;
    return e820_types[type];
}

static void e820_multiboot(void)
{
    physaddr_t mmap_addr, mmap_end;

    if (!(multiboot_info->flags & MULTIBOOT_INFO_MEM_MAP))
        panic("e820 map missing");

    mmap_addr = multiboot_info->mmap_addr;
    mmap_end = mmap_addr + multiboot_info->mmap_length;
    while (mmap_addr < mmap_end) {
        struct multiboot_mmap_entry *e = pa2kva(mmap_addr);
        const char *type = e820_type(e->type);

        pr_info("e820: 0x%016" PRIx64 "-0x%016" PRIx64 ": %s\n", e->addr, e->addr + e->len - 1,
                type);
        if (e->type == E820_RAM)
            bootmem_add(e->addr, e->len);
        mmap_addr += (e->size + 4);
    }

    /* exclude non-RAM */
    mmap_addr = multiboot_info->mmap_addr;
    while (mmap_addr < mmap_end) {
        struct multiboot_mmap_entry *e = pa2kva(mmap_addr);

        if (e->type != E820_RAM)
            bootmem_remove(e->addr, e->len);
        mmap_addr += (e->size + 4);
    }
}

void pmap_init(void)
{
    e820_multiboot();

    /* exclude low & kernel memory */
    bootmem_remove(0, kva2pa(_end));

    pr_info("pmap: _start 0x%016" PRIxPTR "\n", (uintptr_t)_start);
    pr_info("pmap: _etext 0x%016" PRIxPTR "\n", (uintptr_t)_etext);
    pr_info("pmap: _edata 0x%016" PRIxPTR "\n", (uintptr_t)_edata);
    pr_info("pmap: _end   0x%016" PRIxPTR "\n", (uintptr_t)_end);

#if 0
	extern uint64_t kpml4[];
	/* NB: QEMU doesn't support > 1 TB for now */
	for (physaddr_t pa = 0; pa < pa_limit; pa += SZ_1G) {
		void *va = pa2kva(pa);
		uint64_t *pte, *pdpt;

		pte = &kpml4[PML4_INDEX(va)];
		if (*pte & PAGE_P) {
			pdpt = pa2kva(PAGE_ADDR(*pte));
		} else {
			/* allocate a new page for PML3 if needed (> 512 GB) */
			pdpt = bootmem_alloc(SZ_4K, SZ_4K);
			bzero(pdpt, SZ_4K);
			*pte = kva2pa(pdpt) | PAGE_P | PAGE_W;
		}
		pdpt[PDPT_INDEX(va)] = pa | PAGE_P | PAGE_W | PAGE_PS;
	}
#endif
    lcr3(rcr3());
}
