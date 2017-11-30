#include "user.h"

struct cpio_header {
    uint16_t c_magic;
    uint16_t c_dev;
    uint16_t c_ino;
    uint16_t c_mode;
    uint16_t c_uid;
    uint16_t c_gid;
    uint16_t c_nlink;
    uint16_t c_rdev;
    uint16_t c_mtime[2];
    uint16_t c_namesize;
    uint16_t c_filesize[2];
} __packed;

static void extract_dir(const char *name)
{
    char *p = strrchr(name, '/');

    /* create directories if needed */
    if (p) {
        *p = 0;
        extract_dir(name);
        *p = '/';
    }

    mkdir(name, 0777);
}

static void extract_file(const char *name, const void *buf, size_t len)
{
    char *p = strrchr(name, '/');
    int fd;
    ssize_t r;

    /* create directories if needed */
    if (p) {
        *p = 0;
        extract_dir(name);
        *p = '/';
    }

    fd = open(name, O_CREAT | O_WRONLY);
    assert(fd >= 0, "open %s failed: %d", name, fd);
    r = write(fd, buf, len);
    assert(r == len, "write");
    close(fd);
}

int main(int argc, char **argv)
{
    int fd = 0;
    struct cpio_header header;
    char name[128];
    size_t filesize, n;
    ssize_t r;
    char *buf;

    while (1) {
        r = read(fd, &header, sizeof(header));
        assert(r == sizeof(header), "header");
        assert(header.c_magic == 070707, "magic");

        n = header.c_namesize;
        n = (n & 1) ? n + 1 : n;
        r = read(fd, name, n);
        assert(r == n, "name");
        if (strcmp(name, "TRAILER!!!") == 0)
            break;

        filesize = ((uint32_t)header.c_filesize[0] << 16) | header.c_filesize[1];
        dprintf(2, "%10zu %s\n", filesize, name);

        switch (header.c_mode & 0170000) {
        case 0100000:
            /*regular file */
            n = filesize;
            n = (n & 1) ? n + 1 : n;
            buf = malloc(n);
            r = read(fd, buf, n);
            assert(r == n, "file");
            extract_file(name, buf, filesize);
            free(buf);
            break;
        case 0040000:
            /* directory */
            assert(filesize == 0, "directory must be empty");
            extract_dir(name);
            break;
        default:
            assert(false, "unknown file type");
        }
    }

    return 0;
}
