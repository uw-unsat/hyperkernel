#include "user.h"

static const char *proc_state_names[] = {
        [PROC_UNUSED] = "UNUSED  ",  [PROC_EMBRYO] = "EMBRYO  ",   [PROC_RUNNABLE] = "RUNNABLE",
        [PROC_RUNNING] = "RUNNING ", [PROC_SLEEPING] = "SLEEPING", [PROC_ZOMBIE] = "ZOMBIE  ",
};

static void spaces(uint64_t x, size_t n)
{
    size_t i;

    if (x == 0) {
        i = 1;
    } else {
        for (i = 0; x; x /= 10)
            ++i;
    }

    for (; i < n; ++i)
        printf(1, " ");
}

static void ps(void)
{
    pid_t pid;

    printf(1, "  PID  PPID  STATE     NAME\n");

    for (pid = 0; pid < NPROC; ++pid) {
        pid_t ppid = uprocs[pid].ppid;
        int state = uprocs[pid].state;

        if (state == PROC_UNUSED)
            continue;

        /* pid */
        spaces(pid, 5);
        printf(1, "%ld ", pid);

        /* ppid */
        spaces(ppid, 5);
        printf(1, "%ld  ", ppid);

        /* state */
        assert(state < countof(proc_state_names), "state must be valid");
        printf(1, "%s", proc_state_names[state]);

        /* name */
        printf(1, "  %s\n", (char *)&uprocs[pid].name);
    }
}

int main(int argc, char *argv[])
{
    ps();
    exit();
}
