#include "user.h"

static void freelist(void)
{
    static bool freelist[NPAGE];
    pn_t i;
    size_t count;

    for (i = upages[0].link.next, count = 0; i != 0; i = upages[i].link.next) {
        freelist[i] = true;
        assert(upages[i].type == PAGE_TYPE_FREE, "must be free page");
        count++;
    }
    printf(1, "Found %zu free pages in freelist\n", count);

    for (i = 0, count = 0; i < NPAGE; i++)
        if (upages[i].type == PAGE_TYPE_FREE && !freelist[i])
            count++;

    printf(1, "Found %zu free pages not in freelist\n", count);
}

int main(int argc, char *argv[])
{
    freelist();
    exit();
}
