#pragma once

#include <uapi/machine/mmu.h>
#include "types.h"

extern uint64_t pages[NPAGE][PAGE_SIZE / sizeof(uint64_t)];
extern struct page_desc page_desc_table[NPAGE];

void alloc_page(pid_t pid, enum page_type type, pn_t pn);
void free_page(pn_t pn);
int map_page(pid_t pid, pn_t from_pn, size_t index, pn_t pfn, pte_t perm,
             enum page_type from_type);

int sys_alloc_pdpt(pid_t pid, pn_t from, size_t index, pn_t to, pte_t perm);
int sys_alloc_pd(pid_t pid, pn_t from, size_t index, pn_t to, pte_t perm);
int sys_alloc_pt(pid_t pid, pn_t from, size_t index, pn_t to, pte_t perm);
int sys_alloc_frame(pid_t pid, pn_t from, size_t index, pn_t to, pte_t perm);
int sys_copy_frame(pn_t from, pid_t pid, pn_t to);
int sys_protect_frame(pn_t pt, size_t index, pn_t frame, pte_t perm);

int sys_free_pdpt(pn_t from, size_t index, pn_t to);
int sys_free_pd(pn_t from, size_t index, pn_t to);
int sys_free_pt(pn_t from, size_t index, pn_t to);
int sys_free_frame(pn_t from, size_t index, pn_t to);
int sys_reclaim_page(pn_t pn);

int sys_map_page_desc(pid_t pid, pn_t from, size_t index, size_t n, pte_t perm);
int sys_map_pml4(pid_t pid, size_t index, pte_t perm);
int sys_map_proc(pid_t pid, pn_t from, size_t index, size_t n, pte_t perm);
int sys_map_dev(pid_t pid, pn_t from, size_t index, size_t n, pte_t perm);
int sys_map_file(pid_t pid, pn_t from, size_t index, size_t n, pte_t perm);
int sys_map_port(pn_t from, size_t index, size_t n, pte_t perm);

static inline struct page_desc *get_page_desc(pn_t pn)
{
    assert(is_pn_valid(pn), "page number must be valid");
    return &page_desc_table[pn];
}

static inline bool is_page_type(pn_t pn, enum page_type type)
{
    return is_pn_valid(pn) && get_page_desc(pn)->type == type;
}

static inline bool is_page_pid(pn_t pn, pid_t pid)
{
    return is_pn_valid(pn) && get_page_desc(pn)->pid == pid;
}

static inline void *get_page(pn_t pn)
{
    assert(is_pn_valid(pn), "pn must be valid");
    return pages + pn;
}

static inline pn_t pn_to_pfn(pn_t pn)
{
    pn_t pfn0 = (uintptr_t)pages / PAGE_SIZE;

    assert(is_pn_valid(pn), "pn must be valid");
    return pfn0 + pn;
}

static inline pn_t pfn_to_pn(pn_t pfn)
{
    pn_t pfn0 = (uintptr_t)pages / PAGE_SIZE;

    assert(pfn >= pfn0 && pfn < pfn0 + NPAGE, "pfn must be valid");
    return pfn - pfn0;
}
