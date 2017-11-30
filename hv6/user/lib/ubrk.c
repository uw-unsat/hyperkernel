#include "user.h"

static uintptr_t brk_ptr;

static uintptr_t allocuvm(uintptr_t oldsz, uintptr_t newsz)
{
    uintptr_t a;
    pid_t pid = getpid();
    int r;

    assert(oldsz <= newsz, "newsz should be larger");

    a = roundup(oldsz, PAGE_SIZE);
    for (; a < newsz; a += PAGE_SIZE) {
        pn_t pt, frame;

        pt = page_walk(a);
        frame = find_free_page();
        r = sys_alloc_frame(pid, pt, PT_INDEX(a), frame, PTE_P | PTE_W);
        assert(r == 0, "sys_alloc_frame");
    }
    return newsz;
}

static uintptr_t deallocuvm(uintptr_t oldsz, uintptr_t newsz)
{
    uintptr_t a;
    int r;

    assert(oldsz >= newsz, "newsz should be smaller");

    a = roundup(newsz, PAGE_SIZE);
    for (; a < oldsz; a += PAGE_SIZE) {
        pn_t pt, frame;

        pt = page_walk(a);
        frame = virt_to_pn((void *)a);
        r = sys_free_frame(pt, PT_INDEX(a), frame);
        assert(r == 0, "sys_free_frame");
    }
    return newsz;
}

void *sbrk(intptr_t n)
{
    uintptr_t result = brk_ptr, sz = brk_ptr;

    if (n > 0) {
        sz = allocuvm(sz, sz + n);
        assert(sz, "allocuvm failed");
    } else if (n < 0) {
        sz = deallocuvm(sz, sz + n);
    }
    brk_ptr = sz;
    return (void *)result;
}

/* internal use */
void reset_ubrk(uintptr_t va)
{
    brk_ptr = va;
}
