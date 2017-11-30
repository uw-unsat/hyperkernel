#include "user.h"

static void fill(char *indent, size_t from, size_t to, char c)
{
    memset(indent + from, c, to - from);
}

static size_t fill_children(pid_t ppid, pid_t *children)
{
    pid_t pid;
    size_t i = 0;

    memset(children, 0, sizeof(pid_t) * NPROC);
    for (pid = 0; pid < NPROC; ++pid) {
        if (pid != ppid && uprocs[pid].ppid == ppid)
            children[i++] = pid;
    }
    return i;
}

static void pstree(char *indent, pid_t pid)
{
    int level = strlen(indent);
    pid_t children[NPROC] = {0};
    size_t i, idt, num_children;

    num_children = fill_children(pid, children);
    for (i = 0; i < num_children; i++) {
        char *name = (char *)&uprocs[children[i]].name;
        bool first = (i == 0);
        bool last = (i + 1 == num_children);

        if (!first)
            printf(1, "\n%s", indent);

        if (!last)
            memcpy(indent + strlen(indent), "│", 3);

        if (first && last)
            printf(1, "─");
        if (first && !last)
            printf(1, "─┬─");
        if (!first && last)
            printf(1, "└─");
        if (!first && !last)
            printf(1, "├─");

        idt = !first && last ? 3 : 2;

        printf(1, "%s", name);

        fill(indent, strlen(indent), strlen(indent) + strlen(name) + idt, ' ');
        pstree(indent, children[i]);
        fill(indent, level, strlen(indent), '\0');
    }
}

int main(int argc, char *argv[])
{
    /* probably enough */
    char indent[1024] = {0};
    char *name = (char *)&uprocs[1].name;

    printf(1, "%s", name);
    memset(indent, ' ', strlen(name) + 1);
    pstree(indent, 1);
    printf(1, "\n");
    exit();
}
