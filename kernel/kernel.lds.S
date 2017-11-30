#include <machine/memlayout.h>

OUTPUT_ARCH(i386:x86-64)

SECTIONS
{
	. = TEXT_OFFSET;
	_start = .;

	.text : {
		*(.head.text)
		*(.text .text.*)
		_etext = .;
	}

	.rodata : {
		*(.rodata .rodata.*)
	}

	.data : {
		*(.data .data.*)
		_edata = .;
	}

	.bss : {
		*(.bss .bss.*)
	}

	. = ALIGN(SZ_2M);
	_end = .;
}
