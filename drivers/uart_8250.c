#include <uapi/machine/cpufunc.h>
#include <uapi/machine/io.h>
#include <uapi/console.h>

#define COM_RX 0           /* In:	Receive buffer (DLAB=0) */
#define COM_TX 0           /* Out: Transmit buffer (DLAB=0) */
#define COM_DLL 0          /* Out: Divisor Latch Low (DLAB=1) */
#define COM_DLM 1          /* Out: Divisor Latch High (DLAB=1) */
#define COM_IER 1          /* Out: Interrupt Enable Register */
#define COM_IER_RDI 0x01   /* Enable receiver data interrupt */
#define COM_IIR 2          /* In:	Interrupt ID Register */
#define COM_FCR 2          /* Out: FIFO Control Register */
#define COM_LCR 3          /* Out: Line Control Register */
#define COM_LCR_DLAB 0x80  /* Divisor latch access bit */
#define COM_LCR_WLEN8 0x03 /* Wordlength: 8 bits */
#define COM_MCR 4          /* Out: Modem Control Register */
#define COM_MCR_RTS 0x02   /* RTS complement */
#define COM_MCR_DTR 0x01   /* DTR complement */
#define COM_MCR_OUT2 0x08  /* Out2 complement */
#define COM_LSR 5          /* In:	Line Status Register */
#define COM_LSR_DATA 0x01  /* Data available */
#define COM_LSR_TXRDY 0x20 /* Transmit buffer avail */
#define COM_LSR_TSRE 0x40  /* Transmitter off */

struct uart {
    uint16_t com;
    uint8_t irq;
};

static struct uart uarts[] = {
    {PORT_COM2, IRQ_COM2}, {PORT_COM1, IRQ_COM1},
};

int uart8250_getc(void *arg)
{
    struct uart *uart = arg;

    if (!(inb(uart->com + COM_LSR) & COM_LSR_DATA))
        return -1;
    return inb(uart->com + COM_RX);
}

static void uart8250_write(void *arg, const char *s, size_t n)
{
    struct uart *uart = arg;
    size_t i;

    for (i = 0; i < n; ++i) {
        while (!(inb(uart->com + COM_LSR) & COM_LSR_TXRDY))
            pause();
        outb(uart->com + COM_TX, s[i]);
    }
}

void uart8250_init(void)
{
    struct uart *uart = &uarts[1];

    /* turn off the FIFO */
    outb(uart->com + COM_FCR, 0);

    /* set speed; requires DLAB latch */
    outb(uart->com + COM_LCR, COM_LCR_DLAB);
    outb(uart->com + COM_DLL, (uint8_t)(115200 / 9600));
    outb(uart->com + COM_DLM, 0);

    /* 8 data bits, 1 stop bit, parity off; turn off DLAB latch */
    outb(uart->com + COM_LCR, COM_LCR_WLEN8 & ~COM_LCR_DLAB);

    /* no modem controls */
    outb(uart->com + COM_MCR, 0);
    /* enable rcv interrupts */
    outb(uart->com + COM_IER, COM_IER_RDI);

    if (inb(uart->com + COM_LSR) == 0xff) {
        /* serial port doesn't exist */
        return;
    }

    /* clear any preexisting overrun indications and interrupts */
    inb(uart->com + COM_IIR);
    inb(uart->com + COM_RX);

    static struct console_device dev = {.getc = uart8250_getc, .write = uart8250_write};
    dev.arg = uart;
    console_register(&dev);
}
