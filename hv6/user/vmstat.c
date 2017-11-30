#include "user.h"

static const char *typenames[] = {
        [PAGE_TYPE_FREE] = "FREE     ",       [PAGE_TYPE_RESERVED] = "RESERVED ",
        [PAGE_TYPE_PROC_DATA] = "PROC/DATA",  [PAGE_TYPE_FRAME] = "FRAME    ",
        [PAGE_TYPE_X86_PML4] = "PML4     ",   [PAGE_TYPE_X86_PDPT] = "PDPT     ",
        [PAGE_TYPE_X86_PD] = "PD       ",     [PAGE_TYPE_X86_PT] = "PT       ",
        [PAGE_TYPE_IOMMU_PDPT] = "IO/PDPT  ", [PAGE_TYPE_IOMMU_PD] = "IO/PD    ",
        [PAGE_TYPE_IOMMU_PT] = "IO/PT    ",   [PAGE_TYPE_IOMMU_FRAME] = "IO/FRAME ",
        [PAGE_TYPE_IOMMU_PML4] = "IO/PML4  ",
};

static void fill(uint64_t x, size_t n, uint8_t c)
{
    size_t i;

    if (x == 0) {
        i = 1;
    } else {
        for (i = 0; x; x /= 10)
            ++i;
    }

    for (; i < n; ++i)
        printf(1, "%c", c);
}

static void vmstat(void)
{
    pn_t i, n = NPAGE, start = 0;
    pid_t pid;
    int type;

    pid = upages[0].pid;
    type = upages[0].type;

    for (i = 1; i < n; ++i) {
        if (type == upages[i].type && pid == upages[i].pid && i != n - 1)
            continue;
        if (start == i - 1) {
            fill(0, 7, ' ');
        } else {
            fill(start, 5, '0');
            printf(1, "%lu-", start);
        }
        fill((i == n - 1) ? i : i - 1, 5, '0');
        printf(1, "%lu ", (i == n - 1) ? i : i - 1);
        assert(type <= countof(typenames), "must be valid type");
        printf(1, " %s", typenames[type]);
        printf(1, "  ");
        if (pid) {
            fill(pid, 2, '0');
            printf(1, "%ld %.16s", pid, (char *)&uprocs[pid].name);
        }
        printf(1, "\n");
        pid = upages[i].pid;
        type = upages[i].type;
        start = i;
    }
}

int main(int argc, char *argv[])
{
    vmstat();
    exit();
}
