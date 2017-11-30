#include <uapi/machine/cpufunc.h>
#include <uapi/machine/trap.h>

/* I/O Addresses of the two 8259A programmable interrupt controllers */
#define IO_PIC1 0x20 /* master (IRQs 0-7) */
#define IO_PIC2 0xa0 /* slave (IRQs 8-15) */

#define IRQ_SLAVE 2 /* IRQ at which slave connects to master */

static void pic_set_mask(uint16_t mask)
{
    outb(IO_PIC1 + 1, mask);
    outb(IO_PIC2 + 1, mask >> 8);
}

void pic_init(void)
{
    /* mask all interrupts */
    outb(IO_PIC1 + 1, 0xff);
    outb(IO_PIC2 + 1, 0xff);

    /* set up master (8259A-1) */

    /*
     * ICW1: 0001g0hi
     *    g: 0 = edge triggering, 1 = level triggering
     *    h: 0 = cascaded PICs, 1 = master only
     *    i: 0 = no ICW4, 1 = ICW4 required
     */
    outb(IO_PIC1, 0x11);

    /* ICW2: vector offset */
    outb(IO_PIC1 + 1, TRAP_IRQ0);

    /*
     * ICW3: bit mask of IR lines connected to slave PICs (master PIC),
     *       3-bit No of IR line at which slave connects to master(slave PIC).
     */
    outb(IO_PIC1 + 1, 1U << IRQ_SLAVE);

    /*
     * ICW4: 000nbmap
     *    n: 1 = special fully nested mode
     *    b: 1 = buffered mode
     *    m: 0 = slave PIC, 1 = master PIC
     *       (ignored when b is 0, as the master/slave role can be hardwired)
     *    a: 1 = Automatic EOI mode
     *    p: 0 = MCS-80/85 mode, 1 = intel x86 mode
     */
    outb(IO_PIC1 + 1, 0x3);

    /* set up slave (8259A-2) */
    outb(IO_PIC2, 0x11);              /* ICW1 */
    outb(IO_PIC2 + 1, TRAP_IRQ0 + 8); /* ICW2 */
    outb(IO_PIC2 + 1, IRQ_SLAVE);     /* ICW3 */
                                      /*
                                       * NB Automatic EOI mode doesn't tend to work on the slave.
                                       * Linux source code says it's "to be investigated".
                                       */
    outb(IO_PIC2 + 1, 0x01);          /* ICW4 */

    /*
     * OCW3: 0ef01prs
     *   ef: 0x = NOP, 10 = clear specific mask, 11 = set specific mask
     *    p: 0 = no polling, 1 = polling mode
     *   rs: 0x = NOP, 10 = read IRR, 11 = read ISR
    */
    outb(IO_PIC1, 0x68); /* clear specific mask */
    outb(IO_PIC1, 0x0a); /* read IRR by default */

    outb(IO_PIC2, 0x68); /* OCW3 */
    outb(IO_PIC2, 0x0a); /* OCW3 */

    /* initial IRQ mask has interrupt 2 enabled (for slave 8259A) */
    pic_set_mask(0xffff & ~(1U << IRQ_SLAVE));
}
