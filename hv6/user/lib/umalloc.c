#include "param.h"
#include "stat.h"
#include "types.h"
#include "user.h"

#if 1
/*
 * Memory allocator by Kernighan and Ritchie,
 * The C programming Language, 2nd ed.  Section 8.7.
 */

typedef long Align;

union header {
    struct {
        union header *ptr;
        uint64_t size;
    } s;
    Align x;
};

typedef union header Header;

static Header base;
static Header *freep;

void free(void *ap)
{
    Header *bp, *p;

    if (!ap)
        return;
    bp = (Header *)ap - 1;
    for (p = freep; !(bp > p && bp < p->s.ptr); p = p->s.ptr)
        if (p >= p->s.ptr && (bp > p || bp < p->s.ptr))
            break;
    if (bp + bp->s.size == p->s.ptr) {
        bp->s.size += p->s.ptr->s.size;
        bp->s.ptr = p->s.ptr->s.ptr;
    } else
        bp->s.ptr = p->s.ptr;
    if (p + p->s.size == bp) {
        p->s.size += bp->s.size;
        p->s.ptr = bp->s.ptr;
    } else
        p->s.ptr = bp;
    freep = p;
}

static Header *morecore(size_t nu)
{
    char *p;
    Header *hp;

    if (nu < 4096)
        nu = 4096;
    p = sbrk(nu * sizeof(Header));
    if (p == (char *)-1)
        return 0;
    hp = (Header *)p;
    hp->s.size = nu;
    free((void *)(hp + 1));
    return freep;
}

void *malloc(size_t nbytes)
{
    Header *p, *prevp;
    size_t nunits;

    nunits = (nbytes + sizeof(Header) - 1) / sizeof(Header) + 1;
    if ((prevp = freep) == 0) {
        base.s.ptr = freep = prevp = &base;
        base.s.size = 0;
    }
    for (p = prevp->s.ptr;; prevp = p, p = p->s.ptr) {
        if (p->s.size >= nunits) {
            if (p->s.size == nunits)
                prevp->s.ptr = p->s.ptr;
            else {
                p->s.size -= nunits;
                p += p->s.size;
                p->s.size = nunits;
            }
            freep = prevp;
            return (void *)(p + 1);
        }
        if (p == freep)
            if ((p = morecore(nunits)) == 0)
                return 0;
    }
}

void *realloc(void *ap, size_t nbyte)
{
    Header *bp;

    if (!ap)
        return malloc(nbyte);

    bp = (Header *)ap - 1;
    size_t size = (bp->s.size - 1) * sizeof(Header);
    if (size >= nbyte) {
        return ap;
    } else {
        void *new = malloc(nbyte);
        memmove(new, ap, size);
        free(ap);
        return new;
    }
}

void reset_umalloc(void)
{
    memset(&base, 0, sizeof(base));
    freep = NULL;
}

#else

/* a simple page-based allocator, not dependent on sbrk */

#define UVPT_INDEX(va)                                                                             \
    ((va >> PT_SHIFT) & (PTRS_PER_PML4 * PTRS_PER_PDPT * PTRS_PER_PD * PTRS_PER_PT - 1))

#define PTE_CONT 0x200
#define PTE_DONE 0x400

#define HEAP_BASE SZ_512G

static uintptr_t base;

void *malloc(size_t nbytes)
{
    uintptr_t va, result;
    pid_t pid = getpid();
    int r;

    assert(nbytes, "nbytes must be non-zero");

    for (va = base; va - base < nbytes; va += PAGE_SIZE) {
        pn_t pt, frame;
        pte_t perm = PTE_P | PTE_W;

        pt = page_walk(va);
        frame = find_free_page();
        /* not the last page */
        if (va + PAGE_SIZE - base < nbytes)
            perm |= PTE_CONT;
        else
            perm |= PTE_DONE;
        r = sys_alloc_frame(pid, pt, PT_INDEX(va), frame, perm);
        assert(r == 0, "sys_alloc_frame");
    }

    result = base;
    base = va;
    return (void *)result;
}

void free(void *ptr)
{
    uintptr_t va = (uintptr_t)ptr;
    int r;

    if (!ptr)
        return;

    assert(va % PAGE_SIZE == 0, "invalid pointer to free");
    assert(va >= HEAP_BASE && va < base, "pointer out of bounds");
    while (1) {
        pn_t pt;
        pte_t entry = uvpt[UVPT_INDEX(va)];
        int cont = !!(entry & PTE_CONT);

        assert(entry & PTE_P, "must be a valid entry");
        pt = page_walk(va);
        r = sys_free_frame(pt, PT_INDEX(va), virt_to_pn((void *)va));
        assert(r == 0, "sys_free_frame");
        if (!cont) {
            assert(entry & PTE_DONE, "must be the last page");
            break;
        }
        va += PAGE_SIZE;
    }
}

void *realloc(void *ptr, size_t nbyte)
{
    uintptr_t va = (uintptr_t)ptr;
    size_t size = 0;
    void *new;

    if (!ptr)
        return malloc(nbyte);

    assert(va % PAGE_SIZE == 0, "invalid pointer to realloc");
    while (1) {
        pte_t entry = uvpt[UVPT_INDEX(va)];
        int cont = !!(entry & PTE_CONT);

        va += PAGE_SIZE;
        size += PAGE_SIZE;
        if (!cont)
            break;
    }

    if (size >= nbyte)
        return ptr;

    new = malloc(nbyte);
    memcpy(new, ptr, size);
    free(ptr);
    return new;
}

void reset_umalloc(void)
{
    base = HEAP_BASE;
}

#endif
