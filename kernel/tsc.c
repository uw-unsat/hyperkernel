#include <uapi/machine/cpufunc.h>
#include <time.h>

#define IO_TIMER1 0x040 /* 8253 Timer #1 */
#define TIMER_FREQ 1193182
#define TIMER_CNTR (IO_TIMER1 + 0)     /* timer counter port */
#define TIMER_MODE (IO_TIMER1 + 3)     /* timer mode port */
#define TIMER_SEL0 0x00                /* select counter 0 */
#define TIMER_TCOUNT 0x00              /* mode 0, terminal count */
#define TIMER_16BIT 0x30               /* r/w counter 16 bits, LSB first */
#define TIMER_STAT 0xe0                /* read status mode */
#define TIMER_STAT0 (TIMER_STAT | 0x2) /* status mode counter 0 */

static uint64_t tsc_mhz;

void tsc_init(void)
{
    uint64_t xticks, start, end;

    /* PIT countdown from 2^16 - 1 */
    xticks = 0xffff;
    outb(TIMER_MODE, TIMER_SEL0 | TIMER_TCOUNT | TIMER_16BIT);
    outb(IO_TIMER1, xticks % 256);
    outb(IO_TIMER1, xticks / 256);

    /* wait until OUT bit of status byte is set */
    start = rdtsc();
    do {
        outb(TIMER_MODE, TIMER_STAT0);
        if (rdtsc() - start > BIT64(32)) {
            pr_info("tsc: PIT stuck, assuming 2GHz\n");
            tsc_mhz = 2 * 1000;
            return;
        }
    } while (!(inb(TIMER_CNTR) & 0x80));
    end = rdtsc();

    tsc_mhz = ((end - start) * 10) / ((xticks * 10000000) / TIMER_FREQ);
    pr_info("tsc: %" PRIu64 " MHz\n", tsc_mhz);
}

/* convert cyles to nanoseconds:
 *   ns = cycles / (freq / NSEC_PER_SECOND)
 *   ns = cycles * (NSEC_PER_SECOND / freq)
 *   ns = cycles * (10^3 / freq_mhz)
 */
nanoseconds_t cycles_to_ns(cycle_t cycle)
{
    if (!tsc_mhz)
        return 0;
    return cycle * 1000 / tsc_mhz;
}

cycle_t ns_to_cycles(nanoseconds_t ns)
{
    return ns * tsc_mhz / 1000;
}

cycle_t ms_to_cycles(milliseconds_t ms)
{
    return ms * tsc_mhz * 1000;
}

nanoseconds_t uptime(void)
{
    return cycles_to_ns(rdtsc());
}

void nanodelay(nanoseconds_t delay)
{
    uint64_t tsc_delay, start;

    tsc_delay = (tsc_mhz * delay) / 1000;
    start = rdtsc();
    while (rdtsc() - start < tsc_delay)
        pause();
}
