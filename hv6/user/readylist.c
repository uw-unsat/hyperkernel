#include "user.h"

static int is_ready(pid_t pid)
{
    return uprocs[pid].state == PROC_RUNNING || uprocs[pid].state == PROC_RUNNABLE;
}

static void print(pid_t pid, int color)
{
    dprintf(1, "\x1b[38;5;%dm┌────┴─────────────────┐\x1b[0m\n", color);
    dprintf(1, "\x1b[38;5;%dm│%5ld %-16s│\x1b[0m\n", color, pid, (char *)uprocs[pid].name);
    dprintf(1, "\x1b[38;5;%dm└────┬─────────────────┘\x1b[0m\n", color);
}

int main(int argc, char *argv[])
{
    static bool ready[NPROC];
    pid_t pid, current = getpid(), next;
    size_t count;

    pid = current;
    count = 0;
    dprintf(1, "\n");
    do {
        assert(is_ready(pid), "must be ready");
        next = uprocs[pid].ready.next;
        assert(uprocs[next].ready.prev == pid, "must be well-formed");
        print(pid, (pid == current) ? 42 : 255);
        ready[pid] = true;
        count++;
        pid = next;
    } while (pid != current);
    dprintf(1, "\n");
    dprintf(1, "Found %zu ready processes in readylist\n", count);

    for (pid = 0, count = 0; pid < NPROC; ++pid) {
        if (is_ready(pid) && !ready[pid])
            count++;
    }
    dprintf(1, "Found %zu ready processes not in readylist\n", count);

    return 0;
}
