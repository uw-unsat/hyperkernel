#include <uapi/machine/trap.h>
#include <uapi/elf.h>
#include "user.h"

/* pfn of the first page */
static size_t pfn_pages;

static trap_handler_t trap_handlers[256];

void trap_init(void);
void linux_init(void);
noreturn void fs_serve(void);

void ulib_init(void)
{
    pid_t pid;
    int r;
    size_t i, n;

    trap_init();
    reset_trap_handlers();

    /* set the pfn of the first page */
    assert(upages[0].type == PAGE_TYPE_X86_PML4, "page 0 must be the page table root of init");
    pfn_pages = rcr3() / PAGE_SIZE;
    /* safe to use getpid after setting pfn_pages */
    pid = getpid();

    /* set up uvpt */
    r = sys_map_pml4(pid, UVPML4_INDEX, PTE_P);
    assert(r == 0, "sys_map_pml4");

    /* set up uprocs */
    n = bytes_to_pages(NPROC * sizeof(struct proc));
    for (i = 0; i < n; ++i) {
        uintptr_t va;
        pn_t pt;
        int r;

        va = UPROCS_START + i * PAGE_SIZE;
        pt = page_walk(va);
        r = sys_map_proc(pid, pt, PT_INDEX(va), i, PTE_P);
        assert(r == 0, "sys_map_proc");
    }

    /* set up udevs */
    n = bytes_to_pages(NPCIDEV * sizeof(struct pci_dev));
    for (i = 0; i < n; ++i) {
        uintptr_t va;
        pn_t pt;
        int r;

        va = UDEVS_START + i * PAGE_SIZE;
        pt = page_walk(va);
        r = sys_map_dev(pid, pt, PT_INDEX(va), i, PTE_P);
        assert(r == 0, "sys_map_dev");
    }

    /* set up ufiles */
    n = bytes_to_pages(NFILE * sizeof(struct file));
    for (i = 0; i < n; ++i) {
        uintptr_t va;
        pn_t pt;
        int r;

        va = UFILES_START + i * PAGE_SIZE;
        pt = page_walk(va);
        r = sys_map_file(pid, pt, PT_INDEX(va), i, PTE_P);
        assert(r == 0, "sys_map_file");
    }

    /* set up syscall interception */
    linux_init();
}

void trap(struct trap_frame *tf, int trapnum)
{
    trap_handler_t handler = trap_handlers[trapnum];

    if (handler) {
        handler(tf);
        return;
    }

    panic("%s: trap %d err %lu rip 0x%lx addr 0x%lx",
          (char *)&ucurrent->name, trapnum, tf->err, tf->rip, rcr2());
}

void register_trap_handler(uint8_t trapnum, trap_handler_t handler)
{
    trap_handlers[trapnum] = handler;
}

static void trap_invalid_opcode(struct trap_frame *tf)
{
    /*
     * 0f 01 c1 - vmcall
     * 0f 01 d9 - vmmcall
     */
    uint8_t *p = (uint8_t *)tf->rip;

    if ((*p == 0x0f) && (*(p + 1) == 0x01)) {
        if (*(p + 2) == 0xc1)
            *(p + 2) = 0xd9;
        else if (*(p + 2) == 0xd9)
            *(p + 2) = 0xc1;
        return;
    }
}

void reset_trap_handlers(void)
{
    memset(trap_handlers, 0, sizeof(trap_handlers));
    register_trap_handler(TRAP_UD, trap_invalid_opcode);
}

noreturn void panic(const char *fmt, ...)
{
    va_list ap;
    uint64_t *fp;

    cprintf("PANIC(pid %ld): ", getpid());
    va_start(ap, fmt);
    if (fmt) {
        vcprintf(fmt, ap);
        cprintf("\n");
    }
    va_end(ap);

    for (fp = __builtin_frame_address(0); fp; fp = (uint64_t *)fp[0]) {
        uint64_t ip = fp[1];

        cprintf("[<%016" PRIx64 ">]\n", ip);
    }

    if (getpid() != 1)
        exit();
    /* init: stay here for debugging */
    while (1) {
    };
    __builtin_unreachable();
}

pid_t getpid(void)
{
    return upages[phys_to_pn(rcr3())].pid;
}

char *gets(char *buf, size_t max)
{
    size_t i;
    uint8_t c;

    for (i = 0; i + 1 < max;) {
        ssize_t r;

        r = read(1, &c, 1);
        if (r < 1)
            break;
        /* backspace */
        if (c == '\b' || c == '\x7f') {
            if (i > 0) {
                putchar(1, '\b');
                putchar(1, ' ');
                putchar(1, '\b');
                --i;
            }
            continue;
        }
        if (c == '\r')
            c = '\n';
        putchar(1, c);
        buf[i++] = c;
        if (c == '\n')
            break;
    }
    buf[i] = '\0';
    return buf;
}

/* utility */

static void purge_pages(size_t n)
{
    pn_t i = 0;

    while (n) {
        if (upages[i].type != PAGE_TYPE_FREE &&
            uprocs[upages[i].pid].state == PROC_ZOMBIE) {
            int r;

            r = sys_reclaim_page(i);
            assert(r == 0, "sys_reclaim_page");
            assert(upages[i].type == PAGE_TYPE_FREE, "page must be reclaimed");
            --n;
        }
        ++i;
        if (i >= NPAGE)
            panic("OOM");
    }
}

void find_free_pages(size_t n, ...)
{
    va_list args;
    pn_t *ptr;

    va_start(args, n);

    size_t i;
    pn_t p = 0;

    for (i = 0; i < n; ++i) {
        p = upages[p].link.next;

        if (p == 0) {
            /* Out of memory, purge pages and reset */
            purge_pages(n-i);
            p = upages[0].link.next;
        }

        ptr = va_arg(args, pn_t*);
        *ptr = p;
    }

    va_end(args);
}

pn_t find_free_page(void)
{
    pn_t i;

    i = upages[0].link.next;
    if (upages[i].type == PAGE_TYPE_FREE)
        return i;

    purge_pages(1);
    return find_free_page();
}

pn_t find_consecutive_free_pages(size_t n)
{
    pn_t p = 0;

    while (1) {
        p = upages[p].link.next;

        if (p == 0) {
            /* Out of memory, purge pages and reset */
            purge_pages(3);
            p = 0;
            continue;
        }
        if (upages[p + 0].type != PAGE_TYPE_FREE)
            continue;
        if (upages[p + 1].type != PAGE_TYPE_FREE)
            continue;
        if (upages[p + 2].type != PAGE_TYPE_FREE)
            continue;
        break;
    }

    return p;
}

pid_t find_free_pid(void)
{
    static pid_t i = 1;
    int n = 0;

    while (n < 2) {
        ++i;
        if (i == NPROC) {
            i = 2;
            ++n;
        }
        if (uprocs[i].state == PROC_UNUSED)
            return i;
    }
    panic("no free pid");
}

int find_free_fd(int i)
{
    for (; i < NOFILE; ++i) {
        if (ucurrent->ofile[i] == 0)
            return i;
    }
    panic("out of fd");
}

fn_t find_free_fn(void)
{
    static int i;
    int n = 0;

    /* skip 0 */
    while (n < 2) {
        ++i;
        if (i == NFILE) {
            i = 1;
            ++n;
        }
        if (ufiles[i].type == FD_NONE)
            return i;
    }

    panic("file table full");
}

int is_page_mapped(uintptr_t va)
{
    if (!(uvpml4[PML4_INDEX(va)] & PTE_P))
        return false;
    if (!(uvpdpt[(va >> PDPT_SHIFT) & (PTRS_PER_PML4 * PTRS_PER_PDPT - 1)] & PTE_P))
        return false;
    if (!(uvpd[(va >> PD_SHIFT) & (PTRS_PER_PML4 * PTRS_PER_PDPT * PTRS_PER_PD - 1)] & PTE_P))
        return false;
    if (!(uvpt[(va >> PT_SHIFT) & (PTRS_PER_PML4 * PTRS_PER_PDPT * PTRS_PER_PD * PTRS_PER_PT - 1)] &
          PTE_P))
        return false;
    return true;
}

pn_t page_walk(uintptr_t va)
{
    pid_t pid = getpid();
    pte_t entry, perm = PTE_P | PTE_W;
    pn_t pml4, pdpt, pd, pt;
    int r;

    pml4 = phys_to_pn(rcr3());
    entry = uvpml4[PML4_INDEX(va)];
    if (!(entry & PTE_P)) {
        pdpt = find_free_page();
        r = sys_alloc_pdpt(pid, pml4, PML4_INDEX(va), pdpt, perm);
        assert(r == 0, "sys_alloc_pdpt");
    } else {
        pdpt = phys_to_pn(PTE_ADDR(entry));
    }

    entry = uvpdpt[(va >> PDPT_SHIFT) & (PTRS_PER_PML4 * PTRS_PER_PDPT - 1)];
    if (!(entry & PTE_P)) {
        pd = find_free_page();
        r = sys_alloc_pd(pid, pdpt, PDPT_INDEX(va), pd, perm);
        assert(r == 0, "sys_alloc_pd");
    } else {
        pd = phys_to_pn(PTE_ADDR(entry));
    }

    entry = uvpd[(va >> PD_SHIFT) & (PTRS_PER_PML4 * PTRS_PER_PDPT * PTRS_PER_PD - 1)];
    if (!(entry & PTE_P)) {
        pt = find_free_page();
        r = sys_alloc_pt(pid, pd, PD_INDEX(va), pt, perm);
        assert(r == 0, "sys_alloc_pt");
    } else {
        pt = phys_to_pn(PTE_ADDR(entry));
    }

    entry =
        uvpt[(va >> PT_SHIFT) & (PTRS_PER_PML4 * PTRS_PER_PDPT * PTRS_PER_PD * PTRS_PER_PT - 1)];

    return pt;
}

void map_pages(uintptr_t va, size_t n, pte_t perm)
{
    pn_t pt, frame;
    size_t i;
    int r;

    assert(va % PAGE_SIZE == 0, "va must be page-aligned");
    for (i = 0; i < n; i += PAGE_SIZE, va += PAGE_SIZE) {
        pt = page_walk(va);
        frame = find_free_page();
        r = sys_alloc_frame(getpid(), pt, PT_INDEX(va), frame, perm);
        assert(r == 0, "sys_alloc_frame");
    }
}

void protect_pages(uintptr_t va, size_t n, pte_t perm)
{
    pn_t pt;
    size_t i;
    int r;

    for (i = 0; i < n; i += PAGE_SIZE, va += PAGE_SIZE) {
        pte_t entry;

        entry = uvpd[(va >> PD_SHIFT) & (PTRS_PER_PML4 * PTRS_PER_PDPT * PTRS_PER_PD - 1)];
        pt = phys_to_pn(PTE_ADDR(entry));
        r = sys_protect_frame(pt, PT_INDEX(va), virt_to_pn((void *)va), perm);
        assert(r == 0, "sys_protect_frame: %d", r);
    }
}

pn_t phys_to_pn(physaddr_t pa)
{
    pn_t pfn = pa / PAGE_SIZE;

    assert(pfn >= pfn_pages && pfn < pfn_pages + NPAGE, "pa must be in bounds");
    return pfn - pfn_pages;
}

pn_t virt_to_pn(const void *va)
{
    return phys_to_pn(virt_to_phys(va));
}

physaddr_t virt_to_phys(const void *va)
{
    size_t vpn;
    pte_t entry;

    assert((uintptr_t)va % PAGE_SIZE == 0, "va must be page-aligned");
    vpn = ((uintptr_t)va >> PT_SHIFT) &
          (PTRS_PER_PML4 * PTRS_PER_PDPT * PTRS_PER_PD * PTRS_PER_PT - 1);
    entry = uvpt[vpn];
    assert(entry & PTE_P, "page must be present");
    return PTE_ADDR(entry);
}

void alloc_port(uint16_t port)
{
    int r;

    if (!ucurrent->use_io_bitmap) {
        pn_t pn = find_consecutive_free_pages(3);
        r = sys_alloc_io_bitmap(pn + 0, pn + 1, pn + 2);
        assert(r == 0, "sys_alloc_io_bitmap");
    }

    r = sys_alloc_port(port);
    assert(r == 0, "sys_alloc_port");
}

void alloc_ports(uint16_t port, size_t n)
{
    size_t i;

    for (i = 0; i < n; ++i)
        alloc_port(port + i);
}

void set_proc_name(const char *s)
{
    uint64_t name[2] = {0, 0};

    strncpy((char *)&name, s, sizeof(name));
    sys_set_proc_name(name[0], name[1]);
}

int atoi(const char *s)
{
    int n;

    n = 0;
    while ('0' <= *s && *s <= '9')
        n = n * 10 + (*s++) - '0';
    return n;
}

void *memchr(const void *s, int c, size_t n)
{
    if (n != 0) {
        const unsigned char *p = s;

        do {
            if (*p++ == (unsigned char)c)
                return ((void *)(uintptr_t)(p - 1));
        } while (--n != 0);
    }
    return NULL;
}

int memcmp(const void *v1, const void *v2, size_t n)
{
    const unsigned char *s1, *s2;

    s1 = v1;
    s2 = v2;
    while (n-- > 0) {
        if (*s1 != *s2)
            return *s1 - *s2;
        s1++, s2++;
    }
    return 0;
}

void *memcpy(void *dst, const void *src, size_t n)
{
    return memmove(dst, src, n);
}

void *memmove(void *dst, const void *src, size_t n)
{
    const char *s;
    char *d;

    s = src;
    d = dst;
    if (s < d && s + n > d) {
        s += n;
        d += n;
        while (n-- > 0)
            *--d = *--s;
    } else {
        while (n-- > 0)
            *d++ = *s++;
    }

    return dst;
}

void *memset(void *s, int c, size_t n)
{
    char *p = s;

    while (n-- > 0)
        *p++ = c;
    return s;
}

char *strchr(const char *s, int c)
{
    for (; *s; s++) {
        if (*s == c)
            return (char *)s;
    }
    return 0;
}

int strcmp(const char *s1, const char *s2)
{
    for (; *s1 && *s1 == *s2; ++s1, ++s2)
        ;
    return (int)((unsigned char)*s1 - (unsigned char)*s2);
}

char *strcpy(char *s, const char *t)
{
    char *os;

    os = s;
    while ((*s++ = *t++) != 0)
        ;
    return os;
}

size_t strlcpy(char *restrict dst, const char *restrict src, size_t siz)
{
    char *d = dst;
    const char *s = src;
    size_t n = siz;

    /* copy as many bytes as will fit */
    if (n != 0) {
        while (--n != 0) {
            if ((*d++ = *s++) == '\0')
                break;
        }
    }

    /* Not enough room in dst, add NUL and traverse rest of src */
    if (n == 0) {
        if (siz != 0)
            *d = '\0'; /* NUL-terminate dst */
        while (*s++)
            ;
    }

    return (s - src - 1); /* count does not include NUL */
}

char *strncpy(char *restrict dst, const char *restrict src, size_t n)
{
    size_t i;
    char *retval = dst;

    for (i = 0; i < n; ++i) {
        *dst++ = *src;
        /* NULL pad the remaining bytes */
        if (*src != 0)
            ++src;
    }
    return retval;
}

char *strcat(char *restrict s, const char *restrict append)
{
    char *save = s;

    for (; *s; ++s)
        ;
    while ((*s++ = *append++) != 0)
        ;
    return save;
}

size_t strlen(const char *s)
{
    size_t n;

    for (n = 0; s[n]; n++)
        ;
    return n;
}

int strncmp(const char *p, const char *q, size_t n)
{
    while (n > 0 && *p && *p == *q)
        n--, p++, q++;
    if (n == 0)
        return 0;
    return (unsigned char)*p - (unsigned char)*q;
}

char *strrchr(const char *s, int c)
{
    char *result = NULL, *p;

    for (p = (char *)s;; ++p) {
        p = strchr(p, c);
        if (!p)
            break;
        result = p;
    }
    return result;
}

const char *strerror(int err)
{
    switch (-err) {
    case EPERM: return "EPERM";
    case ENOENT: return "ENOENT";
    case ESRCH: return "ESRCH";
    case EINTR: return "EINTR";
    case EIO: return "EIO";
    case ENXIO: return "ENXIO";
    case E2BIG: return "E2BIG";
    case ENOEXEC: return "ENOEXEC";
    case EBADF: return "EBADF";
    case ECHILD: return "ECHILD";
    case EAGAIN: return "EAGAIN";
    case ENOMEM: return "ENOMEM";
    case EACCES: return "EACCES";
    case EFAULT: return "EFAULT";
    case ENOTBLK: return "ENOTBLK";
    case EBUSY: return "EBUSY";
    case EEXIST: return "EEXIST";
    case EXDEV: return "EXDEV";
    case ENODEV: return "ENODEV";
    case ENOTDIR: return "ENOTDIR";
    case EISDIR: return "EISDIR";
    case EINVAL: return "EINVAL";
    case ENFILE: return "ENFILE";
    case EMFILE: return "EMFILE";
    case ENOTTY: return "ENOTTY";
    case ETXTBSY: return "ETXTBSY";
    case EFBIG: return "EFBIG";
    case ENOSPC: return "ENOSPC";
    case ESPIPE: return "ESPIPE";
    case EROFS: return "EROFS";
    case EMLINK: return "EMLINK";
    case EPIPE: return "EPIPE";
    case EDOM: return "EDOM";
    case ERANGE: return "ERANGE";

    case ENAMETOOLONG: return "ENAMETOOLONG";
    case ENOLCK: return "ENOLCK";

    case ENOSYS: return "ENOSYS";

    case ENOTEMPTY: return "ENOTEMPTY";
    case ELOOP: return "ELOOP";
    case ENOMSG: return "ENOMSG";
    case EIDRM: return "EIDRM";
    case ECHRNG: return "ECHRNG";
    case EL2NSYNC: return "EL2NSYNC";
    case EL3HLT: return "EL3HLT";
    case EL3RST: return "EL3RST";
    case ELNRNG: return "ELNRNG";
    case EUNATCH: return "EUNATCH";
    case ENOCSI: return "ENOCSI";
    case EL2HLT: return "EL2HLT";
    case EBADE: return "EBADE";
    case EBADR: return "EBADR";
    case EXFULL: return "EXFULL";
    case ENOANO: return "ENOANO";
    case EBADRQC: return "EBADRQC";
    case EBADSLT: return "EBADSLT";

    case EDEADLOCK: return "EDEADLOCK";

    case EBFONT: return "EBFONT";
    case ENOSTR: return "ENOSTR";
    case ENODATA: return "ENODATA";
    case ETIME: return "ETIME";
    case ENOSR: return "ENOSR";
    case ENONET: return "ENONET";
    case ENOPKG: return "ENOPKG";
    case EREMOTE: return "EREMOTE";
    case ENOLINK: return "ENOLINK";
    case EADV: return "EADV";
    case ESRMNT: return "ESRMNT";
    case ECOMM: return "ECOMM";
    case EPROTO: return "EPROTO";
    case EMULTIHOP: return "EMULTIHOP";
    case EDOTDOT: return "EDOTDOT";
    case EBADMSG: return "EBADMSG";
    case EOVERFLOW: return "EOVERFLOW";
    case ENOTUNIQ: return "ENOTUNIQ";
    case EBADFD: return "EBADFD";
    case EREMCHG: return "EREMCHG";
    case ELIBACC: return "ELIBACC";
    case ELIBBAD: return "ELIBBAD";
    case ELIBSCN: return "ELIBSCN";
    case ELIBMAX: return "ELIBMAX";
    case ELIBEXEC: return "ELIBEXEC";
    case EILSEQ: return "EILSEQ";
    case ERESTART: return "ERESTART";
    case ESTRPIPE: return "ESTRPIPE";
    case EUSERS: return "EUSERS";
    case ENOTSOCK: return "ENOTSOCK";
    case EDESTADDRREQ: return "EDESTADDRREQ";
    case EMSGSIZE: return "EMSGSIZE";
    case EPROTOTYPE: return "EPROTOTYPE";
    case ENOPROTOOPT: return "ENOPROTOOPT";
    case EPROTONOSUPPORT: return "EPROTONOSUPPORT";
    case ESOCKTNOSUPPORT: return "ESOCKTNOSUPPORT";
    case EOPNOTSUPP: return "EOPNOTSUPP";
    case EPFNOSUPPORT: return "EPFNOSUPPORT";
    case EAFNOSUPPORT: return "EAFNOSUPPORT";
    case EADDRINUSE: return "EADDRINUSE";
    case EADDRNOTAVAIL: return "EADDRNOTAVAIL";
    case ENETDOWN: return "ENETDOWN";
    case ENETUNREACH: return "ENETUNREACH";
    case ENETRESET: return "ENETRESET";
    case ECONNABORTED: return "ECONNABORTED";
    case ECONNRESET: return "ECONNRESET";
    case ENOBUFS: return "ENOBUFS";
    case EISCONN: return "EISCONN";
    case ENOTCONN: return "ENOTCONN";
    case ESHUTDOWN: return "ESHUTDOWN";
    case ETOOMANYREFS: return "ETOOMANYREFS";
    case ETIMEDOUT: return "ETIMEDOUT";
    case ECONNREFUSED: return "ECONNREFUSED";
    case EHOSTDOWN: return "EHOSTDOWN";
    case EHOSTUNREACH: return "EHOSTUNREACH";
    case EALREADY: return "EALREADY";
    case EINPROGRESS: return "EINPROGRESS";
    case ESTALE: return "ESTALE";
    case EUCLEAN: return "EUCLEAN";
    case ENOTNAM: return "ENOTNAM";
    case ENAVAIL: return "ENAVAIL";
    case EISNAM: return "EISNAM";
    case EREMOTEIO: return "EREMOTEIO";
    case EDQUOT: return "EDQUOT";

    case ENOMEDIUM: return "ENOMEDIUM";
    case EMEDIUMTYPE: return "EMEDIUMTYPE";
    case ECANCELED: return "ECANCELED";
    case ENOKEY: return "ENOKEY";
    case EKEYEXPIRED: return "EKEYEXPIRED";
    case EKEYREVOKED: return "EKEYREVOKED";
    case EKEYREJECTED: return "EKEYREJECTED";

    case EOWNERDEAD: return "EOWNERDEAD";
    case ENOTRECOVERABLE: return "ENOTRECOVERABLE";

    case ERFKILL: return "ERFKILL";

    case EHWPOISON: return "EHWPOISON";

    default: return "UNRECOGNIZED ERROR";
    }
}

uint32_t sys_now(void)
{
    static uint64_t tsc_khz;

    if (!tsc_khz)
        tsc_khz = sys_debug_sysctl(SYSCTL_TSC_KHZ);
    return rdtsc() / tsc_khz;
}

void microdelay(uint64_t delay)
{
    uint64_t start;

    start = sys_now();
    while (sys_now() - start < delay)
        pause();
}
