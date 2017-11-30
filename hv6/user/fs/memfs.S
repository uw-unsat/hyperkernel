#if ENABLED(CONFIG_MEMFS)

#include <uapi/machine/mmu.h>

.section .data

.global	_binary_fs_img_start
.global	_binary_fs_img_end

.balign	PAGE_SIZE
_binary_fs_img_start:
	.incbin	"fs.img"
_binary_fs_img_end:

#endif /* CONFIG_MEMFS */
