#include "bench.h"
#include "user.h"

#define MAP_ADDR 0x400000000000

static char *mem;
unsigned long trap_tsc, overhead;
unsigned long time = 0;

static void prime_memory(void)
{
    int i;

    for (i = 0; i < NRPGS * 2; i++) {
        mem[i * PAGE_SIZE] = i;
    }
}

static void benchmark_syscall(void)
{
    int i;
    unsigned long t0;

    synch_tsc();
    t0 = rdtscll();
    for (i = 0; i < N; i++) {
        int ret;

        asm volatile("movq $0, %%rax\n\t" /* nop */
                     "vmcall\n\t"
                     "mov %%eax, %0\n\t"
                     : "=r"(ret)
                     :
                     : "rax");
    }

    printf(1, "System call took %ld cycles\n", (rdtscllp() - t0 - overhead) / N);
}

static void benchmark1_handler(struct trap_frame *tf)
{
    uintptr_t addr = rcr2();

    addr = rounddown(addr, PAGE_SIZE);
    time += rdtscllp() - trap_tsc;

    protect_pages(addr, PAGE_SIZE, PTE_P | PTE_W);
    protect_pages(addr + PAGE_SIZE * NRPGS, PAGE_SIZE, PTE_P);
}

static void benchmark1(void)
{
    int i;

    for (i = 0; i < NRPGS; i++) {
        trap_tsc = rdtscll();
        mem[i * PAGE_SIZE] = i;
    }
}

static void benchmark_appel1(void)
{
    int i;
    unsigned long tsc, avg_appel1 = 0, avg_user_fault = 0;

    register_trap_handler(TRAP_PF, benchmark1_handler);

    for (i = 0; i < N; i++) {
        protect_pages(MAP_ADDR, PAGE_SIZE * NRPGS, PTE_P);

        synch_tsc();
        time = 0;
        tsc = rdtscll();
        benchmark1();

        avg_appel1 += rdtscllp() - tsc - overhead;
        avg_user_fault += (time - overhead * NRPGS) / NRPGS;
    }

    printf(1, "User fault took %ld cycles\n", avg_user_fault / N);
    printf(1, "PROT1,TRAP,UNPROT took %ld cycles\n", avg_appel1 / N);
}

static void benchmark2_handler(struct trap_frame *tf)
{
    uintptr_t addr = rcr2();

    addr = rounddown(addr, PAGE_SIZE);
    protect_pages(addr, PAGE_SIZE, PTE_P | PTE_W);
}

static void benchmark2(void)
{
    int i;

    protect_pages(MAP_ADDR, PAGE_SIZE * NRPGS, PTE_P);

    for (i = 0; i < NRPGS; i++) {
        mem[i * PAGE_SIZE] = i;
    }
}

static void benchmark_appel2(void)
{
    int i;
    unsigned long tsc, avg = 0;

    register_trap_handler(TRAP_PF, benchmark2_handler);

    for (i = 0; i < N; i++) {
        protect_pages(MAP_ADDR, PAGE_SIZE * NRPGS * 2, PTE_P | PTE_W);
        prime_memory();

        synch_tsc();
        tsc = rdtscll();
        benchmark2();
        avg += rdtscllp() - tsc - overhead;
    }

    printf(1, "PROTN,TRAP,UNPROT took %ld cycles\n", avg / N);
}

int main(void)
{
    printf(1, "Starting benchmark...\n");
    overhead = measure_tsc_overhead();
    printf(1, "TSC overhead is %ld\n", overhead);

    printf(1, "Benchmarking hv6 performance...\n");

    benchmark_syscall();

    map_pages(MAP_ADDR, 2 * NRPGS * PAGE_SIZE, PTE_P | PTE_W);

    mem = (void *)MAP_ADDR;
    prime_memory();

    benchmark_appel1();
    benchmark_appel2();

    exit();
}
