#include <uapi/machine/cpufunc.h>
#include <uapi/machine/trap.h>

#define IOREGSEL (0x00 / 4)
#define IOWIN (0x10 / 4)

#define IOAPICID 0x00  /* Register index: ID */
#define IOAPICVER 0x01 /* Register index: version */
#define IOREDTBL 0x10  /* Redirection table base */

#define INT_DISABLED 0x00010000  /* Interrupt disabled */
#define INT_LEVEL 0x00008000     /* Level-triggered (vs edge-) */
#define INT_ACTIVELOW 0x00002000 /* Active low (vs high) */
#define INT_LOGICAL 0x00000800   /* Destination is CPU id (vs APIC ID) */

static uint32_t *ioapic = (void *)0xfec00000;

static uint32_t ioapic_read(int reg)
{
    mmio_write32(ioapic + IOREGSEL, reg);
    return mmio_read32(ioapic + IOWIN);
}

static void ioapic_write(int reg, uint32_t data)
{
    mmio_write32(ioapic + IOREGSEL, reg);
    mmio_write32(ioapic + IOWIN, data);
}

void ioapic_init(void)
{
    int i, reg_ver, ver, pins;

    reg_ver = ioapic_read(IOAPICVER);
    ver = reg_ver & 0xff;
    pins = ((reg_ver >> 16) & 0xff) + 1;
    pr_info("ioapic: 0x%016" PRIxPTR " v%02x [global_irq %02d-%02d]\n",
            (uintptr_t)ioapic, ver, 0, pins - 1);

    /* mark all interrupts edge-triggered, active high, disabled, and not routed to any CPUs */
    for (i = 0; i < pins; ++i) {
        ioapic_write(IOREDTBL + 2 * i, INT_DISABLED | (TRAP_IRQ0 + i));
        ioapic_write(IOREDTBL + 2 * i + 1, 0);
    }
}

void ioapic_enable(int irq, uint32_t apicid)
{
    /*
     * Mark interrupt edge-triggered, active high,
     * enabled, and routed to the given cpunum,
     * which happens to be that cpu's APIC ID.
     */
    ioapic_write(IOREDTBL + 2 * irq, TRAP_IRQ0 + irq);
    ioapic_write(IOREDTBL + 2 * irq + 1, apicid << 24);
    pr_info("ioapic: enable irq %d\n", irq);
}
