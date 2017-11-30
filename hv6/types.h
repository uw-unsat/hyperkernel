#pragma once

#include <uapi/machine/mmu.h>
#include <uapi/bitset.h>
#include <uapi/errno.h>
#include <uapi/pci.h>
#include "param.h"

#define NULLPID 0
#define INITPID 1
#define FSPID 2
#define NSPID 3

enum {
    DEV_CONSOLE = 1,
};

typedef uint64_t pn_t;    /* page number */
typedef uint64_t dmapn_t; /* DMA page number */
typedef uint64_t fn_t;    /* file number */
typedef uint64_t pte_t;   /* page table entry */
typedef int64_t off_t;    /* offset */
typedef uint16_t devid_t; /* PCI device ID */
typedef size_t socklen_t;
typedef uint64_t iommu_pte_t;

enum page_type {
    PAGE_TYPE_FREE = 0,
    PAGE_TYPE_RESERVED,
    PAGE_TYPE_PROC_DATA,
    PAGE_TYPE_FRAME,
    PAGE_TYPE_X86_PML4,
    PAGE_TYPE_X86_PDPT,
    PAGE_TYPE_X86_PD,
    PAGE_TYPE_X86_PT,
    PAGE_TYPE_IOMMU_PML4,
    PAGE_TYPE_IOMMU_PDPT,
    PAGE_TYPE_IOMMU_PD,
    PAGE_TYPE_IOMMU_PT,
    PAGE_TYPE_IOMMU_FRAME,

    /* hack to force 64bit */
    PAGE_TYPE_FORCE_WIDTH = 0xfffffffffffffffful,
};

#define FREELIST_INIT(arr, member, i)               \
({                                                  \
    typeof(&arr->member) entry = &arr[i].member;    \
    entry->next = i;                                \
    entry->prev = i;                                \
})

/* insert new after head */
#define FREELIST_ADD(arr, member, new, head)        \
({                                                  \
    typeof(&arr->member) enew = &arr[new].member;   \
    typeof(&arr->member) ehead = &arr[head].member; \
    enew->next = ehead->next;                       \
    enew->prev = head;                              \
    arr[enew->next].member.prev = new;              \
    ehead->next = new;                              \
})

/* insert new before head */
#define FREELIST_ADD_TAIL(arr, member, new, head)   \
({                                                  \
    typeof(&arr->member) enew = &arr[new].member;   \
    typeof(&arr->member) ehead = &arr[head].member; \
    enew->next = head;                              \
    enew->prev = ehead->prev;                       \
    arr[enew->prev].member.next = new;              \
    ehead->prev = new;                              \
})

#define FREELIST_DEL(arr, member, i)                \
({                                                  \
    typeof(&arr->member) entry = &arr[i].member;    \
    arr[entry->next].member.prev = entry->prev;     \
    arr[entry->prev].member.next = entry->next;     \
    entry->next = entry->prev = 0;                  \
})

struct page_desc {
    enum page_type type : 64;
    pid_t pid;
    struct {
        pn_t prev;
        pn_t next;
    } link;
};

enum proc_state {
    PROC_UNUSED = 0,
    PROC_EMBRYO,
    PROC_RUNNABLE,
    PROC_RUNNING,
    PROC_SLEEPING,
    PROC_ZOMBIE,

    /* hack to force 64bit */
    PROC_STATE_FORCE_WIDTH = 0xfffffffffffffffful,
};

struct proc {
    enum proc_state state : 64; /* process state  */
    pid_t ppid;
    pn_t page_table_root; /* page table root */
    pn_t stack;           /* kernel stack */
    pn_t hvm;
    pn_t io_bitmap_a;
    pn_t io_bitmap_b;
    fn_t ofile[NOFILE]; /* open files */
    size_t nr_children;
    size_t nr_fds;
    size_t nr_pages;
    size_t nr_dmapages;
    size_t nr_devs;
    size_t nr_ports;
    size_t nr_vectors;
    size_t nr_intremaps;
    int launched;
    int killed;
    int use_io_bitmap;
    pid_t ipc_from;
    uint64_t ipc_val;
    pn_t ipc_page;
    size_t ipc_size;
    int ipc_fd;
    BITSET_DEFINE(intr, 256);
    uint64_t name[2]; /* process name (debugging) */
    struct {
        pid_t prev;
        pid_t next;
    } ready;      /* ready queue for runnable/running processes */
};

enum file_type {
    FD_NONE = 0,
    FD_PIPE,
    FD_INODE,
    FD_SOCKET,

    FD_FORCE_WIDTH = 0xfffffffffffffffful,
};

struct file {
    enum file_type type;
    size_t refcnt;
    uint64_t value;
    uint64_t omode;
    size_t offset;
};

#define pci_dev pci_func

enum intremap_state {
    IR_FREE = 0,
    IR_ACTIVE,

    IR_FORCE_WIDTH = ~UINT64_C(0),
};

struct intremap {
    enum intremap_state state;
    devid_t devid;
    uint8_t vector;
};

static inline size_t bytes_to_pages(size_t n)
{
    return roundup(n, PAGE_SIZE) / PAGE_SIZE;
}

static inline bool is_pid_valid(pid_t pid)
{
    return pid > 0 && pid < NPROC;
}

static inline bool is_pn_valid(pn_t pn)
{
    return pn < NPAGE;
}

static inline bool is_page_index_valid(size_t index)
{
    return index < 512;
}

static inline bool is_fd_valid(int fd)
{
    return fd >= 0 && fd < NOFILE;
}

static inline bool is_fn_valid(fn_t fn)
{
    return fn > 0 && fn < NFILE;
}

static inline bool is_dmapn_valid(dmapn_t dmapn)
{
    return dmapn < NDMAPAGE;
}

static inline int is_pfn_pcipn(pn_t pfn)
{
    return pfn >= PCI_START / PAGE_SIZE && pfn < PCI_END / PAGE_SIZE;
}

static inline pn_t pfn_to_pcipn(pn_t pfn)
{
    assert(is_pfn_pcipn(pfn), "pfn must be valid!");
    return pfn - PCI_START / PAGE_SIZE;
}
