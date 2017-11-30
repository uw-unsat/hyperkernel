#include "user.h"

static char buf[PAGE_SIZE] __aligned(PAGE_SIZE);

int main(int argc, char **argv)
{
    int r;
    size_t offset = 0;

    while (1) {
        r = sys_debug_dmesg(virt_to_phys(buf), sizeof(buf), offset);
        if (r <= 0)
            break;
        write(1, buf, r);
        offset += r;
    }

    return 0;
}
