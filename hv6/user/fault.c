#include "user.h"

static void test(struct trap_frame *tf)
{
    dprintf(2, "fault: address 0x%016" PRIx64 "\n", rcr2());
    inb(0);
}

int main(int argc, char **argv)
{
    volatile int *p = NULL;

    register_trap_handler(TRAP_PF, test);
    *p = 0xdead;
    exit();
}
