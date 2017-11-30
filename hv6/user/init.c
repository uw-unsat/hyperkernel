#include "user.h"

noreturn void fs_main(void);

noreturn void main(void)
{
    pid_t pid;
    int r;

    set_proc_name("init");

    /* start file server */
    pid = fork();
    if (!pid)
        fs_main();
    /* wait until fs starts */
    assert(pid == FSPID, "fs pid must be FSPID");
    while (uprocs[pid].state != PROC_SLEEPING)
        yield();

    /* start network server */
    pid = spawnl("ns", "ns", NULL);
    /* wait until ns starts */
    assert(pid == NSPID, "ns pid must be NSPID");
    while (uprocs[pid].state != PROC_SLEEPING && uprocs[pid].state != PROC_ZOMBIE)
        yield();

    /* stdin */
    r = open("console", O_RDWR);
    if (r < 0) {
        r = mknod("console", DEV_CONSOLE, 0);
        assert(r == 0, "mknod");
        r = open("console", O_RDWR);
    }
    assert(r == 0, "open: 0");

    /* stdout */
    r = dup(0);
    assert(r == 1, "dup: 0 -> 1");

    /* stderr */
    r = dup(0);
    assert(r == 2, "dup: 0 -> 2");

    /* run unittests from kernel command line */
    if (is_page_mapped(UCMDLINE)) {
        char *p;

        p = strchr((void *)(uintptr_t)UCMDLINE, ' ');
        if (p && *(p + 1)) {
            cprintf("init: run %s\n", p + 1);
            r = system(p + 1);
            sys_debug_exit(r);
        }
    }

    /* start app servers */
    if (uprocs[NSPID].state != PROC_ZOMBIE) {
        dprintf(1, "init: starting httpd\n");
        spawnl("httpd", "httpd", NULL);
        dprintf(1, "init: starting vncd\n");
        spawnl("vncd", "vncd", NULL);
    }

    /* start sh */
    dprintf(1, "init: starting sh\n");
    while (1) {
        pid = spawnl("sh", "sh", NULL);
        while (pid != wait())
            ;
    }
    panic("TBD");
}
