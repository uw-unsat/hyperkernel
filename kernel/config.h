#pragma once

#define ENABLED(feature) (feature != 0)
#define DISABLED(feature) (feature == 0)

#define CONFIG_X86_64 1
#define CONFIG_X86 1
#define CONFIG_FPU 1

#define CONFIG_PREEMPT_TIMER 100 /* milliseconds */

#define CONFIG_PREEMPT 0

#define CONFIG_VPID 0

/* Enable one of the following */
#define CONFIG_MEMFS 1
#define CONFIG_NVME 0

#if (CONFIG_MEMFS == CONFIG_NVME)
#error "Enable exactly one of MEMFS and NVME"
#endif

#define CONFIG_CGA 1
