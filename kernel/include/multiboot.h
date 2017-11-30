#pragma once

#include <uapi/cdefs.h>

/* headers */
#define MULTIBOOT_HEADER_MAGIC 0x1BADB002
#define MULTIBOOT_PAGE_ALIGN 0x00000001
#define MULTIBOOT_MEMORY_INFO 0x00000002
#define MULTIBOOT_VIDEO_INFO 0x00000004
#define MULTIBOOT_AOUT_KLUDGE 0x00010000

/* entry magic */
#define MULTIBOOT_BOOTLOADER_MAGIC 0x2BADB002

/* flags for struct multiboot_info */
#define MULTIBOOT_INFO_MEMORY 0x00000001
#define MULTIBOOT_INFO_BOOTDEV 0x00000002
#define MULTIBOOT_INFO_CMDLINE 0x00000004
#define MULTIBOOT_INFO_MODS 0x00000008
#define MULTIBOOT_INFO_AOUT_SYMS 0x00000010
#define MULTIBOOT_INFO_ELF_SHDR 0x00000020
#define MULTIBOOT_INFO_MEM_MAP 0x00000040
#define MULTIBOOT_INFO_DRIVE_INFO 0x00000080
#define MULTIBOOT_INFO_CONFIG_TABLE 0x00000100
#define MULTIBOOT_INFO_BOOT_LOADER_NAME 0x00000200
#define MULTIBOOT_INFO_APM_TABLE 0x00000400
#define MULTIBOOT_INFO_VIDEO_INFO 0x00000800

#define E820_RAM 1
#define E820_RESERVED 2
#define E820_ACPI 3
#define E820_NVS 4
#define E820_UNUSABLE 5

#ifndef __ASSEMBLER__

struct multiboot_header {
    uint32_t magic;
    uint32_t flags;
    uint32_t checksum;
    /* valid if MULTIBOOT_AOUT_KLUDGE is set */
    uint32_t header_addr;
    uint32_t load_addr;
    uint32_t load_end_addr;
    uint32_t bss_end_addr;
    uint32_t entry_addr;
    /* valid if MULTIBOOT_VIDEO_MODE is set */
    uint32_t mode_type;
    uint32_t width;
    uint32_t height;
    uint32_t depth;
} __attribute__((packed));

struct multiboot_aout_symbol_table {
    uint32_t tabsize;
    uint32_t strsize;
    uint32_t addr;
    uint32_t reserved;
} __packed;

struct multiboot_elf_section_header_table {
    uint32_t num;
    uint32_t size;
    uint32_t addr;
    uint32_t shndx;
} __packed;

struct multiboot_info {
    uint32_t flags;
    uint32_t mem_lower;
    uint32_t mem_upper;
    uint32_t boot_device;
    uint32_t cmdline;
    uint32_t mods_count;
    uint32_t mods_addr;
    union {
        struct multiboot_aout_symbol_table aout_sym;
        struct multiboot_elf_section_header_table elf_sec;
    };
    uint32_t mmap_length;
    uint32_t mmap_addr;
    uint32_t drives_length;
    uint32_t drives_addr;
    uint32_t config_table;
    uint32_t boot_loader_name;
    uint32_t apm_table;
    uint32_t vbe_control_info;
    uint32_t vbe_mode_info;
    uint16_t vbe_mode;
    uint16_t vbe_interface_seg;
    uint16_t vbe_interface_off;
    uint16_t vbe_interface_len;
} __packed;

struct multiboot_mmap_entry {
    uint32_t size;
    uint64_t addr;
    uint64_t len;
    uint32_t type;
} __packed;

struct multiboot_mod_list {
    uint32_t mod_start;
    uint32_t mod_end;
    uint32_t cmdline;
    uint32_t pad;
} __packed;

/* saved in locore.S */
extern struct multiboot_info *multiboot_info;

#endif /* !__ASSEMBLER__ */
