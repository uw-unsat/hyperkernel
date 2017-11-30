#pragma once

#include <uapi/machine/cpufunc.h>
#include <uapi/machine/io.h>
#include <uapi/machine/mmu.h>
#include <uapi/machine/trap.h>
#include <uapi/errno.h>
#include <uapi/sysctl.h>
#include "fcntl.h"
#include "memlayout.h"
#include "readline.h"
#include "stat.h"
#include "syscall.h"
#include "types.h"

#define uvpml4 ((pte_t *)UVPML4)
#define uvpdpt ((pte_t *)UVPDPT)
#define uvpd ((pte_t *)UVPD)
#define uvpt ((pte_t *)UVPT)
#define upages ((struct page_desc *)UPAGES_START)
#define uprocs ((struct proc *)UPROCS_START)
#define ucurrent (uprocs + getpid())
#define udevs ((struct pci_dev *)UDEVS_START)
#define ufiles ((struct file *)UFILES_START)
#define uecam ((void *)UECAM_START)

#define AF_UNSPEC 0
#define AF_INET 2
#define AF_INET6 10
#define PF_INET AF_INET
#define PF_INET6 AF_INET6
#define PF_UNSPEC AF_UNSPEC

#define IPPROTO_IP 0
#define IPPROTO_TCP 6
#define IPPROTO_UDP 17
#define IPPROTO_IPV6 41

#define SOCK_STREAM 1
#define SOCK_DGRAM 2
#define SOCK_RAW 3

#define SOL_SOCKET 0xfff
#define SO_ERROR 0x1007
#define SO_TYPE 0x1008

noreturn void sys_debug_exit(int);
void sys_debug_print_console(physaddr_t addr, size_t len);
void sys_debug_print_screen(physaddr_t addr, size_t len);
int sys_debug_dmesg(physaddr_t addr, size_t len, size_t offset);

int sys_map_page_desc(pid_t pid, pn_t pt, size_t index, size_t n, pte_t perm);
int sys_map_pml4(pid_t pid, size_t index, pte_t perm);
int sys_map_proc(pid_t pid, pn_t pt, size_t index, size_t n, pte_t perm);
int sys_map_proc(pid_t pid, pn_t from, size_t index, size_t n, pte_t perm);
int sys_map_dev(pid_t pid, pn_t from, size_t index, size_t n, pte_t perm);
int sys_map_file(pid_t pid, pn_t from, size_t index, size_t n, pte_t perm);

int sys_alloc_pdpt(pid_t pid, pn_t pml4, size_t index, pn_t pdpt, pte_t perm);
int sys_alloc_pd(pid_t pid, pn_t pdpt, size_t index, pn_t pd, pte_t perm);
int sys_alloc_pt(pid_t pid, pn_t pd, size_t index, pn_t pt, pte_t perm);
int sys_alloc_frame(pid_t pid, pn_t pt, size_t index, pn_t frame, pte_t perm);
int sys_copy_frame(pn_t from, pid_t pid, pn_t to);
int sys_protect_frame(pn_t pt, size_t index, pn_t frame, pte_t perm);

int sys_free_pdpt(pn_t from, size_t index, pn_t to);
int sys_free_pd(pn_t from, size_t index, pn_t to);
int sys_free_pt(pn_t from, size_t index, pn_t to);
int sys_free_frame(pn_t from, size_t index, pn_t to);
int sys_reclaim_page(pn_t pn);

/* avoid a ret to ensure a child process to return to the right place */
static __always_inline int sys_clone(pid_t pid, pn_t pml4, pn_t stack, pn_t hvm)
{
    int r;

    asm volatile("vmcall"
                 : "=a"(r)
                 : "D"(pid), "S"(pml4), "d"(stack), "c"(hvm), "a"(SYS_clone)
                 : "cc", "memory");
    return r;
}
int sys_set_proc_name(uint64_t name0, uint64_t name1);
int sys_set_runnable(pid_t pid);
int sys_switch(pid_t pid);
int sys_kill(pid_t pid);
int sys_reap(pid_t pid);
int sys_reparent(pid_t pid);

int sys_map_pcipage(pn_t pt, size_t index, pn_t pcipn, pte_t perm);
int sys_alloc_iommu_root(devid_t devid, pn_t pn);
int sys_alloc_iommu_pdpt(pn_t from, size_t index, pn_t to, iommu_pte_t perm);
int sys_alloc_iommu_pd(pn_t from, size_t index, pn_t to, iommu_pte_t perm);
int sys_alloc_iommu_pt(pn_t from, size_t index, pn_t to, iommu_pte_t perm);
int sys_alloc_iommu_frame(pn_t from, size_t index, dmapn_t to, iommu_pte_t perm);
int sys_map_iommu_frame(pn_t pt, size_t index, dmapn_t to, pte_t perm);
int sys_reclaim_iommu_frame(dmapn_t dmapn);
int sys_reclaim_iommu_root(devid_t devid);

int sys_alloc_vector(uint8_t vector);
int sys_reclaim_vector(uint8_t vector);

int sys_alloc_intremap(size_t index, devid_t devid, uint8_t vector);
int sys_reclaim_intremap(size_t index);
int sys_ack_intr(uint8_t irq);

int sys_send(pid_t pid, uint64_t val, pn_t pn, size_t size, int fd);
int sys_recv(pid_t pid, pn_t pn, int fd);
int sys_reply_wait(pid_t pid, uint64_t val, pn_t inpn, size_t size, int infd, pn_t outpn);
int sys_call(pid_t pid, uint64_t val, pn_t inpn, size_t size, pn_t outpn, int outfd);

int sys_create(int fd, fn_t fn, int type, uint64_t value, uint64_t omode);
int sys_close(pid_t pid, int fd);
int sys_dup(int oldfd, pid_t pid, int newfd);
int sys_dup2(int oldfd, pid_t pid, int newfd);
int sys_lseek(int fd, off_t offset);

int sys_alloc_io_bitmap(pn_t pn1, pn_t pn2, pn_t pn3);
int sys_alloc_port(uint16_t port);
int sys_reclaim_port(uint16_t port);

uint64_t sys_debug_sysctl(uint64_t id);

int putchar(int fd, uint8_t c);
void vdprintf(int, const char *, va_list) __printf(2, 0);
void dprintf(int, const char *, ...) __printf(2, 3);
void vsnprintf(char *str, size_t size, const char *fmt, va_list ap) __printf(3, 0);
void snprintf(char *str, size_t size, const char *fmt, ...) __printf(3, 4);
void vcprintf(const char *, va_list ap) __printf(1, 0);
void cprintf(const char *, ...) __printf(1, 2);

/* xv6 compatible */
#define vprintf vdprintf
#define printf dprintf

pid_t getpid(void);
pid_t fork(void);
noreturn void exit(void);
int kill(pid_t);
pid_t wait(void);
void yield(void);

int exec(const char *path, char *argv[]);
int execl(const char *path, const char *arg0, ...);
int fexec(int fd, char *argv[]);
pid_t spawn(const char *path, char *argv[]);
pid_t spawnl(const char *path, const char *arg0, ...);
int system(const char *cmd);

int chdir(const char *path);
int close(int fd);
int dup(int fd);
int dup2(int oldfd, int newfd);
int fchdir(int fd);
int fstat(int fd, struct stat *st);
int fstatat(int dirfd, const char *pathname, struct stat *st);
int isatty(int fd);
int mkdir(const char *path, int mode);
int mknod(const char *path, short major, short minor);
int openat(int dirfd, const char *path, int omode);
int open(const char *path, int omode);
ssize_t pread(int fd, void *buf, size_t len, off_t offset);
ssize_t pwrite(int fd, const void *buf, size_t len, off_t offset);
ssize_t read(int fd, void *buf, size_t len);
int stat(const char *path, struct stat *st);
ssize_t write(int fd, const void *buf, size_t len);
int unlink(const char *path);
int unlinkat(int dirfd, const char *pathname, int flags);

int pipe(int fds[2]);

/* for vnc */
void *membuf(int *pos);

void *sbrk(intptr_t increment);
void *malloc(size_t);
void *realloc(void *ap, size_t);
void free(void *);

char *gets(char *buf, size_t max);

/* ulib utility */
void find_free_pages(size_t n, ...);
pn_t find_free_page(void);
pn_t find_consecutive_free_pages(size_t n);
pid_t find_free_pid(void);
int find_free_fd(int i);
static inline int find_lowest_free_fd(void)
{
    return find_free_fd(0);
}
fn_t find_free_fn(void);
pn_t phys_to_pn(physaddr_t pa);
pn_t virt_to_pn(const void *va);
physaddr_t virt_to_phys(const void *va);

struct file *fd_to_file(int fd);

int is_page_mapped(uintptr_t va);
pn_t page_walk(uintptr_t va);
void map_pages(uintptr_t va, size_t n, pte_t perm);
void protect_pages(uintptr_t va, size_t n, pte_t perm);
void reset_ubrk(uintptr_t va);
void reset_umalloc(void);

typedef void (*trap_handler_t)(struct trap_frame *);
void register_trap_handler(uint8_t trapnum, trap_handler_t f);
void reset_trap_handlers(void);

void alloc_port(uint16_t port);
void alloc_ports(uint16_t port, size_t n);
void set_proc_name(const char *s);
void debug_print_console(const void *s, size_t n);
void debug_print_screen(const void *s, size_t n);

int atoi(const char *s);
void *memchr(const void *s, int c, size_t n);
int memcmp(const void *v1, const void *v2, size_t n);
void *memcpy(void *dst, const void *src, size_t n);
void *memmove(void *dst, const void *src, size_t n);
void *memset(void *s, int c, size_t n);
char *strchr(const char *s, int c);
int strcmp(const char *s, const char *t);
char *strcpy(char *s, const char *t);
size_t strlcpy(char *restrict dst, const char *restrict src, size_t dstsize);
size_t strlen(const char *s);
int strncmp(const char *p, const char *q, size_t n);
char *strncpy(char *restrict dst, const char *restrict src, size_t n);
char *strcat(char *restrict s, const char *restrict append);
char *strrchr(const char *s, int c);

const char *strerror(int err);

/* for lwip */
uint32_t sys_now(void);
void microdelay(uint64_t delay);
