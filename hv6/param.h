#pragma once

#include <uapi/machine/io.h>

#define NPAGE 8192  /* maximum number of pages */
#define NDMAPAGE 512 /* maximum number of DMA pages */
#define NPROC 64    /* maximum number of processes */
#define NTSLICE 128 /* Number of scheduler timeslices */
#define NOFILE 16   /* open files per process */
#define NFILE 128   /* open files per system */
#define MAXARG 32   /* max exec arguments */
#define MAXPATH 256 /* max path length */
#define NPCIDEV 64  /* maximum number of PCI devices */
#define NINTREMAP 8 /* maximum number of interrupt remapping entries */
#define NPCIPAGE ((PCI_END - PCI_START) / PAGE_SIZE)
