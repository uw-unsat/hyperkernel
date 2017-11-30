#include "fs.h"

char *fmtname(char *path)
{
    static char buf[16];
    char *p;

    /* find first character after last slash */
    for (p = path + strlen(path); p >= path && *p != '/'; p--)
        ;
    p++;

    /* return blank-padded name */
    if (strlen(p) >= sizeof(buf) - 1)
        return p;
    memmove(buf, p, strlen(p));
    memset(buf + strlen(p), ' ', sizeof(buf) - 1 - strlen(p));
    return buf;
}

void ls(char *path)
{
    char buf[512], *p;
    int fd;
    struct dirent de;
    struct stat st;

    if ((fd = open(path, 0)) < 0) {
        printf(2, "ls: cannot open %s\n", path);
        return;
    }

    if (fstat(fd, &st) < 0) {
        printf(2, "ls: cannot stat %s\n", path);
        close(fd);
        return;
    }

    switch (st.type) {
    case T_FILE:
        printf(1, "%s %d %u %u\n", fmtname(path), st.type, st.ino, st.size);
        break;

    case T_DIR:
        if (strlen(path) + 1 + DIRSIZ + 1 > sizeof buf) {
            printf(1, "ls: path too long\n");
            break;
        }
        strcpy(buf, path);
        p = buf + strlen(buf);
        *p++ = '/';
        while (read(fd, &de, sizeof(de)) == sizeof(de)) {
            if (de.inum == 0)
                continue;
            memmove(p, de.name, DIRSIZ);
            p[DIRSIZ] = 0;
            if (stat(buf, &st) < 0) {
                printf(1, "ls: cannot stat %s\n", buf);
                continue;
            }
            printf(1, "%s %d %u %u\n", fmtname(buf), st.type, st.ino, st.size);
        }
        break;
    }
    close(fd);
}

int main(int argc, char *argv[])
{
    int i;

    if (argc < 2) {
        ls(".");
        exit();
    }
    for (i = 1; i < argc; i++)
        ls(argv[i]);
    exit();
}
