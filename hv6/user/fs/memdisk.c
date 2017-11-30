#if ENABLED(CONFIG_MEMFS)

#include "fs.h"

extern char _binary_fs_img_start[], _binary_fs_img_end[];

void unix_init(void)
{
    pr_info("fs: use memfs\n");
}

void unix_read(uint64_t block, void *buf)
{
    memcpy(buf, _binary_fs_img_start + block * BSIZE, BSIZE);
}

void unix_write(uint64_t block, const void *buf)
{
    memcpy(_binary_fs_img_start + block * BSIZE, buf, BSIZE);
}

void unix_flush(void)
{
}
#endif /* CONFIG_MEMFS */
