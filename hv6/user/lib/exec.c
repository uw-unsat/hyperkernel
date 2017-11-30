#include <uapi/elf.h>
#include "user.h"

static char argv_data[PAGE_SIZE];

static int copy_argv(char *dst_argv[], char *src_argv[]);
static void clear_lower_pml4(void);

noreturn void do_fexec(int fd, char *argv[])
{
    int argc;
    char *saved_argv[MAXARG] = {NULL};
    char buf[PAGE_SIZE] __aligned(PAGE_SIZE);
    struct elf64_ehdr *ehdr;
    struct elf64_phdr *phdr;
    size_t phnum, i;
    uintptr_t entry;
    ssize_t ni, n;

    /* copy argv before tearing down the lower half */
    argc = copy_argv(saved_argv, argv);

    /* tear down the lower half */
    clear_lower_pml4();

    /* read the first data block for the elf header */
    n = pread(fd, buf, sizeof(buf), 0);
    ehdr = (void *)buf;
    /* too restrictive (>= 4K) but works for now */
    if (n != sizeof(buf) || !IS_ELF(*ehdr)) {
        dprintf(2, "invalid elf file\n");
        exit();
    }
    phnum = ehdr->e_phnum;
    entry = ehdr->e_entry;

    /* assume all program headers fit in one page for simplicity */
    assert(ehdr->e_phoff + sizeof(struct elf64_phdr) * phnum <= PAGE_SIZE,
           "too many program headers");
    phdr = (void *)buf + ehdr->e_phoff;
    for (i = 0; i < phnum; ++i, ++phdr) {
        uint64_t va, end_fileva, end_memva;

        if (phdr->p_type != PT_LOAD)
            continue;
        va = phdr->p_vaddr;
        end_fileva = va + phdr->p_filesz;
        end_memva = va + phdr->p_memsz;
        assert(end_fileva <= end_memva, "file size must be no larger than memory size");
        assert(end_memva >= va, "must not overflow in elf");
        assert(end_memva < UINT64_C(0x800000000000), "must be in lower half");

        /* assume there's no overlap between sections */
        map_pages(rounddown(va, PAGE_SIZE), end_memva - rounddown(va, PAGE_SIZE), PTE_P | PTE_W);
        n = 0;
        while (n < phdr->p_filesz) {
            ni = pread(fd, (void *)va + n, phdr->p_filesz - n, phdr->p_offset + n);
            assert(ni >= 0, "pread");
            n += ni;
        }
        assert(n == phdr->p_filesz, "pread");
    }

    /* close fds with O_CLOEXEC */
    for (i = 0; i < NOFILE; ++i) {
        fn_t fn;

        fn = ucurrent->ofile[i];
        if (!is_fn_valid(fn))
            continue;
        if (ufiles[fn].omode & O_CLOEXEC)
            close(i);
    }

    /* set name for debugging */
    set_proc_name(saved_argv[0]);

    /*
     * Reset the program break. We should probably choose the end of
     * the data segment, but let's just set it to some random value.
     */
    reset_ubrk(UBRK_START);
    reset_umalloc();
    reset_history();

    /* reset trap handlers */
    reset_trap_handlers();

    /* map the initial user stack */
    map_pages(USTACK_TOP - USTACK_SIZE, USTACK_SIZE, PTE_P | PTE_W);

    /*
     * According to the abi, the initial stack after exec should be:
     *   content		address
     *   ------------------------------
     *   NULL		... (we don't have envp)
     *   NULL		8*argc+%rsp
     *   ...		...
     *   argv[0]		8+%rsp
     *   argc		%rsp
     */
    memcpy((void *)USTACK_TOP - PAGE_SIZE, &argc, 8);
    memcpy((void *)USTACK_TOP - PAGE_SIZE + 8, saved_argv, argc * 8);

    /*
     * According the abi, most registers are unspecified, except for:
     *   %rsp: point to the structure above
     *   %rdx: function pointer for application to register with atexit
     */
    asm volatile("movq %0, %%rsp; jmpq *%1"
                 :
                 : "i"(USTACK_TOP - PAGE_SIZE), "r"(entry), "d"(0)
                 : "memory", "cc");
    __builtin_unreachable();
}

/* called by exec in usys.S */
int do_exec(const char *path, char *argv[])
{
    int fd;

    fd = open(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0)
        return fd;

    do_fexec(fd, argv);
}

int execl(const char *path, const char *arg0, ...)
{
    va_list ap;
    size_t n;
    char *args[MAXARG];

    va_start(ap, arg0);
    args[0] = (char *)arg0;
    for (n = 1; n < MAXARG && args[n - 1]; ++n) {
        args[n] = va_arg(ap, char *);
    }
    va_end(ap);

    if (args[n - 1])
        panic("args are not null-terminated");

    return exec(path, args);
}

pid_t spawn(const char *path, char *argv[])
{
    pid_t pid;

    pid = fork();
    if (pid == 0) {
        exec(argv[0], argv);
        assert(false, "exec");
    }
    return pid;
}

pid_t spawnl(const char *path, const char *arg0, ...)
{
    va_list ap;
    size_t n;
    char *args[MAXARG];

    va_start(ap, arg0);
    args[0] = (char *)arg0;
    for (n = 1; n < MAXARG && args[n - 1]; ++n) {
        args[n] = va_arg(ap, char *);
    }
    va_end(ap);

    if (args[n - 1])
        panic("args are not null-terminated");

    return spawn(path, args);
}

int system(const char *cmd)
{
    pid_t pid;
    char *argv[MAXARG + 1];
    char *p;
    size_t i;

    strlcpy(argv_data, cmd, sizeof(argv_data));
    p = argv_data;
    for (i = 0; i < MAXARG; ++i) {
        argv[i] = p;
        p = strchr(p, ' ');
        if (!p) {
            argv[++i] = NULL;
            break;
        }
        *p = 0;
        ++p;
    }

    pid = spawn(argv[0], argv);
    while (1) {
        if (wait() == pid)
            break;
    }
    return 0;
}

static int copy_argv(char *dst_argv[], char *src_argv[])
{
    char *p = argv_data, *end = argv_data + sizeof(argv_data);
    int argc = 0;

    for (; src_argv[argc]; ++argc) {
        size_t count;

        assert(argc < MAXARG, "too many arguments");
        assert(p < end, "arguments too long");
        count = strlcpy(p, src_argv[argc], end - p);
        dst_argv[argc] = p;
        p += count + 1;
    }
    return argc;
}

static void clear_pt(pn_t pt, size_t n)
{
    size_t i;
    int r;

    for (i = 0; i < PTRS_PER_PT; ++i) {
        pte_t entry;
        pn_t pn;

        entry = uvpt[n + i];
        if (!(entry & PTE_P))
            continue;
        pn = phys_to_pn(PTE_ADDR(entry));
        /* other types (page_desc, proc, etc.) are mapped in higher half */
        assert(upages[pn].type == PAGE_TYPE_FRAME, "must be frame");
        r = sys_free_frame(pt, i, pn);
        assert(r == 0, "sys_free_frame");
    }
}

static void clear_pd(pn_t pd, size_t n)
{
    size_t i;
    int r;

    for (i = 0; i < PTRS_PER_PD; ++i) {
        pte_t entry;
        pn_t pn;

        entry = uvpd[n + i];
        if (!(entry & PTE_P))
            continue;
        pn = phys_to_pn(PTE_ADDR(entry));
        assert(upages[pn].type == PAGE_TYPE_X86_PT, "must be pt");
        clear_pt(pn, (n + i) * PTRS_PER_PD);
        r = sys_free_pt(pd, i, pn);
        assert(r == 0, "sys_free_pt");
    }
}

static void clear_pdpt(pn_t pdpt, size_t n)
{
    size_t i;
    int r;

    for (i = 0; i < PTRS_PER_PDPT; ++i) {
        pte_t entry;
        pn_t pn;

        entry = uvpdpt[n + i];
        if (!(entry & PTE_P))
            continue;
        pn = phys_to_pn(PTE_ADDR(entry));
        assert(upages[pn].type == PAGE_TYPE_X86_PD, "must be pd");
        clear_pd(pn, (n + i) * PTRS_PER_PDPT);
        r = sys_free_pd(pdpt, i, pn);
        assert(r == 0, "sys_free_pd");
    }
}

static void clear_lower_pml4(void)
{
    pn_t pml4 = phys_to_pn(rcr3());
    size_t i;
    int r;

    for (i = 0; i < PTRS_PER_PML4 / 2; ++i) {
        pte_t entry;
        pn_t pn;

        entry = uvpml4[i];
        if (!(entry & PTE_P))
            continue;

        /* ignore the uvpt entry as it's in the higher half */
        pn = phys_to_pn(PTE_ADDR(entry));
        assert(upages[pn].type == PAGE_TYPE_X86_PDPT, "must be pdpt");
        clear_pdpt(pn, i * PTRS_PER_PML4);
        r = sys_free_pdpt(pml4, i, pn);
        assert(r == 0, "sys_free_pdpt");
    }
}
