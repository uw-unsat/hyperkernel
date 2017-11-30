#include <uapi/console.h>
#include "device.h"
#include "fd.h"
#include "ioport.h"
#include "ipc.h"
#include "mmap.h"
#include "proc.h"
#include "syscall.h"
#include "vm.h"

extern int sys_debug_exit(int r);

extern uint64_t sys_debug_sysctl(uint64_t id);

static int sys_nop(void)
{
    return -ENOSYS;
}

static void *debug_print_check(physaddr_t addr, size_t len)
{
    void *p = pa2kva(addr);
    pn_t pn;

    assert(len <= PAGE_SIZE - addr % PAGE_SIZE, "must be within a page");
    pn = pfn_to_pn(addr / PAGE_SIZE);
    assert(is_page_pid(pn, current), "must be from current");
    assert(is_page_type(pn, PAGE_TYPE_FRAME), "must be frame");

    return p;
}

static void sys_debug_print_console(physaddr_t addr, size_t len)
{
    console_write(debug_print_check(addr, len), len);
}

static void sys_debug_print_screen(physaddr_t addr, size_t len)
{
    cga_write(pa2kva(CGA_START), debug_print_check(addr, len), len);
}

static int sys_debug_dmesg(physaddr_t addr, size_t len, off_t offset)
{
    pn_t pn;

    assert(len <= PAGE_SIZE - addr % PAGE_SIZE, "sys_debug_dmesg");
    pn = pfn_to_pn(addr / PAGE_SIZE);
    assert(is_page_pid(pn, current), "must be from current");
    assert(is_page_type(pn, PAGE_TYPE_FRAME), "must be frame");

    return syslog_read(pa2kva(addr), len, offset);
}

void *syscalls[NR_syscalls] = {
        [0 ... NR_syscalls - 1] = sys_nop,
        [SYS_map_pml4] = sys_map_pml4,
        [SYS_map_page_desc] = sys_map_page_desc,
        [SYS_map_proc] = sys_map_proc,
        [SYS_map_dev] = sys_map_dev,
        [SYS_map_file] = sys_map_file,
        [SYS_alloc_pdpt] = sys_alloc_pdpt,
        [SYS_alloc_pd] = sys_alloc_pd,
        [SYS_alloc_pt] = sys_alloc_pt,
        [SYS_alloc_frame] = sys_alloc_frame,
        [SYS_copy_frame] = sys_copy_frame,
        [SYS_protect_frame] = sys_protect_frame,
        [SYS_free_pdpt] = sys_free_pdpt,
        [SYS_free_pd] = sys_free_pd,
        [SYS_free_pt] = sys_free_pt,
        [SYS_free_frame] = sys_free_frame,
        [SYS_reclaim_page] = sys_reclaim_page,
        [SYS_clone] = sys_clone,
        [SYS_set_proc_name] = sys_set_proc_name,
        [SYS_set_runnable] = sys_set_runnable,
        [SYS_switch] = sys_switch,
        [SYS_kill] = sys_kill,
        [SYS_reap] = sys_reap,
        [SYS_reparent] = sys_reparent,
        [SYS_send] = sys_send,
        [SYS_recv] = sys_recv,
        [SYS_reply_wait] = sys_reply_wait,
        [SYS_call] = sys_call,
        [SYS_create] = sys_create,
        [SYS_close] = sys_close,
        [SYS_dup] = sys_dup,
        [SYS_dup2] = sys_dup2,
        [SYS_lseek] = sys_lseek,
        [SYS_map_pcipage] = sys_map_pcipage,
        [SYS_alloc_iommu_root] = sys_alloc_iommu_root,
        [SYS_alloc_iommu_pdpt] = sys_alloc_iommu_pdpt,
        [SYS_alloc_iommu_pd] = sys_alloc_iommu_pd,
        [SYS_alloc_iommu_pt] = sys_alloc_iommu_pt,
        [SYS_alloc_iommu_frame] = sys_alloc_iommu_frame,
        [SYS_map_iommu_frame] = sys_map_iommu_frame,
        [SYS_reclaim_iommu_frame] = sys_reclaim_iommu_frame,
        [SYS_reclaim_iommu_root] = sys_reclaim_iommu_root,
        [SYS_alloc_vector] = sys_alloc_vector,
        [SYS_reclaim_vector] = sys_reclaim_vector,
        [SYS_alloc_intremap] = sys_alloc_intremap,
        [SYS_reclaim_intremap] = sys_reclaim_intremap,
        [SYS_ack_intr] = sys_ack_intr,
        [SYS_alloc_io_bitmap] = sys_alloc_io_bitmap,
        [SYS_alloc_port] = sys_alloc_port,
        [SYS_reclaim_port] = sys_reclaim_port,
        [SYS_debug_exit] = sys_debug_exit,
        [SYS_debug_print_console] = sys_debug_print_console,
        [SYS_debug_print_screen] = sys_debug_print_screen,
        [SYS_debug_dmesg] = sys_debug_dmesg,
        [SYS_debug_sysctl] = sys_debug_sysctl,
};
