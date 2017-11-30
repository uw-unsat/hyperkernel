#include <bootmem.h>
#include <string.h>
#include <symtable.h>

struct bootmem_map bootmem_map;

static int sealed;

static bool overlap(struct region r0, struct region r1)
{
    if (r1.upper - 1 < r0.lower || r0.upper - 1 < r1.lower)
        return false;
    return true;
}

static bool subset(struct region r0, struct region r1)
{
    if (r0.lower >= r1.lower && r0.upper - 1 <= r1.upper - 1)
        return true;
    return false;
}

static bool empty(struct region r)
{
    return r.lower == r.upper;
}

static struct region *lastp(void)
{
    if (bootmem_map.size > 0)
        return &bootmem_map.regions[bootmem_map.size - 1];
    return NULL;
}

static void clear(struct region *rp)
{
    /* remove trailing empty slots */
    for (; bootmem_map.size > 0; --bootmem_map.size) {
        if (!empty(*lastp()))
            break;
    }
    /* swap with the last slot */
    if (bootmem_map.size > 0) {
        *rp = *lastp();
        bzero(lastp(), sizeof(*rp));
        --bootmem_map.size;
        return;
    }
    /* empty map */
    bzero(rp, sizeof(*rp));
}

static void append(struct region r)
{
    size_t i = 0, n = bootmem_map.size;
    struct region *rp = bootmem_map.regions;

    if (empty(r))
        return;

    /* find an empty slot */
    for (; i < n; ++i, ++rp) {
        if (empty(*rp))
            break;
    }

    if (i == n) {
        if (i >= BOOTMEM_MAP_MAX_SIZE)
            panic("too many regions");
        ++bootmem_map.size;
    }
    *rp = r;
}

void bootmem_add(physaddr_t addr, size_t size)
{
    struct region r = {addr, addr + size};
    size_t i = 0, n = bootmem_map.size;

    if (empty(r))
        return;

    for (; i < n; ++i) {
        struct region *rp = bootmem_map.regions + i;

        /* ignore if not overlapped */
        if (empty(*rp) || !overlap(r, *rp))
            continue;
        /* merge two regions */
        addr = min(r.lower, rp->lower);
        size = max(r.upper - 1, rp->upper - 1) + 1 - addr;
        /* remove the old region */
        clear(rp);
        /* recursively add and merge */
        bootmem_add(addr, size);
        return;
    }

    /* default add: no overlap */
    append(r);
}

void bootmem_remove(physaddr_t addr, size_t size)
{
    struct region r = {addr, addr + size};
    size_t i = 0, n = bootmem_map.size;

    if (empty(r))
        return;

    for (; i < n; ++i) {
        struct region *rp = bootmem_map.regions + i;

        /* ignore if not overlapped */
        if (empty(*rp) || !overlap(r, *rp))
            continue;
        /* remove a region if it's covered */
        if (subset(*rp, r)) {
            clear(rp);
            bootmem_remove(addr, size);
            return;
        }
        /* break a region into two if it covers the given one */
        if (subset(r, *rp)) {
            struct region r1 = {r.upper, rp->upper};

            /* first subregion [rp->lower, r.lower) */
            rp->upper = r.lower;
            /* second subregion [r.upper, rp->upper) */
            append(r1);
            return;
        }
        /* shrink the lower part */
        if (r.lower < rp->lower) {
            rp->lower = r.upper;
            return;
        }
        /* shrink the upper part */
        if (r.upper - 1 < rp->upper - 1) {
            rp->upper = r.upper;
            return;
        }
        assert(false, "unreachable");
    }
}

bool bootmem_usable(physaddr_t addr, size_t size)
{
    struct region r = {addr, addr + size};
    size_t i = 0, n = bootmem_map.size;
    struct region *rp = bootmem_map.regions;

    /* check if it is within some usable region  */
    for (; i < n; ++i, ++rp) {
        /* usable region */
        if (!empty(*rp) && subset(r, *rp))
            return true;
    }
    return false;
}

void *bootmem_alloc(size_t alignment, size_t size)
{
    size_t i = 0, n = bootmem_map.size;
    struct region *rp = bootmem_map.regions;

    assert(!sealed, "bootmem in use");
    for (; i < n; ++i, ++rp) {
        physaddr_t base = roundup(rp->lower, alignment);
        struct region r = {base, base + size};

        if (subset(r, *rp)) {
            bootmem_remove(base, size);
            return pa2kva(base);
        }
    }
    panic("out of memory");
}

void bootmem_seal(void)
{
    sealed = true;
}
