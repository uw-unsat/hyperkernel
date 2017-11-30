#include <uapi/machine/cpufunc.h>
#include <uapi/console.h>

/* special keycodes */
#define KEY_HOME 0xE0
#define KEY_END 0xE1
#define KEY_UP 0xE2
#define KEY_DN 0xE3
#define KEY_LF 0xE4
#define KEY_RT 0xE5
#define KEY_PGUP 0xE6
#define KEY_PGDN 0xE7
#define KEY_INS 0xE8
#define KEY_DEL 0xE9

/* This is i8042reg.h + kbdreg.h from NetBSD. */

#define KBSTATP 0x64   /* kbd controller status port(I) */
#define KBS_DIB 0x01   /* kbd data in buffer */
#define KBS_IBF 0x02   /* kbd input buffer low */
#define KBS_WARM 0x04  /* kbd input buffer low */
#define KBS_OCMD 0x08  /* kbd output buffer has command */
#define KBS_NOSEC 0x10 /* kbd security lock not engaged */
#define KBS_TERR 0x20  /* kbd transmission error or from mouse */
#define KBS_RERR 0x40  /* kbd receive error */
#define KBS_PERR 0x80  /* kbd parity error */

#define KBCMDP 0x64         /* kbd controller port(O) */
#define KBC_RAMREAD 0x20    /* read from RAM */
#define KBC_RAMWRITE 0x60   /* write to RAM */
#define KBC_AUXDISABLE 0xa7 /* disable auxiliary port */
#define KBC_AUXENABLE 0xa8  /* enable auxiliary port */
#define KBC_AUXTEST 0xa9    /* test auxiliary port */
#define KBC_KBDECHO 0xd2    /* echo to keyboard port */
#define KBC_AUXECHO 0xd3    /* echo to auxiliary port */
#define KBC_AUXWRITE 0xd4   /* write to auxiliary port */
#define KBC_SELFTEST 0xaa   /* start self-test */
#define KBC_KBDTEST 0xab    /* test keyboard port */
#define KBC_KBDDISABLE 0xad /* disable keyboard port */
#define KBC_KBDENABLE 0xae  /* enable keyboard port */
#define KBC_PULSE0 0xfe     /* pulse output bit 0 */
#define KBC_PULSE1 0xfd     /* pulse output bit 1 */
#define KBC_PULSE2 0xfb     /* pulse output bit 2 */
#define KBC_PULSE3 0xf7     /* pulse output bit 3 */

#define KBDATAP 0x60 /* kbd data port(I) */
#define KBOUTP 0x60  /* kbd data port(O) */

#define K_RDCMDBYTE 0x20
#define K_LDCMDBYTE 0x60

#define KC8_TRANS 0x40    /* convert to old scan codes */
#define KC8_MDISABLE 0x20 /* disable mouse */
#define KC8_KDISABLE 0x10 /* disable keyboard */
#define KC8_IGNSEC 0x08   /* ignore security lock */
#define KC8_CPU 0x04      /* exit from protected mode reset */
#define KC8_MENABLE 0x02  /* enable mouse interrupt */
#define KC8_KENABLE 0x01  /* enable keyboard interrupt */
#define CMDBYTE (KC8_TRANS | KC8_CPU | KC8_MENABLE | KC8_KENABLE)

/* keyboard commands */
#define KBC_RESET 0xFF      /* reset the keyboard */
#define KBC_RESEND 0xFE     /* request the keyboard resend the last byte */
#define KBC_SETDEFAULT 0xF6 /* resets keyboard to its power-on defaults */
#define KBC_DISABLE 0xF5    /* as per KBC_SETDEFAULT, but also disable key scanning */
#define KBC_ENABLE 0xF4     /* enable key scanning */
#define KBC_TYPEMATIC 0xF3  /* set typematic rate and delay */
#define KBC_SETTABLE 0xF0   /* set scancode translation table */
#define KBC_MODEIND 0xED    /* set mode indicators(i.e. LEDs) */
#define KBC_ECHO 0xEE       /* request an echo from the keyboard */

/* keyboard responses */
#define KBR_EXTENDED 0xE0 /* extended key sequence */
#define KBR_RESEND 0xFE   /* needs resend of command */
#define KBR_ACK 0xFA      /* received a valid command */
#define KBR_OVERRUN 0x00  /* flooded */
#define KBR_FAILURE 0xFD  /* diagnosic failure */
#define KBR_BREAK 0xF0    /* break code prefix - sent on key release */
#define KBR_RSTDONE 0xAA  /* reset complete */
#define KBR_ECHO 0xEE     /* echo response */

#define NO 0

#define SHIFT (1 << 0)
#define CTL (1 << 1)
#define ALT (1 << 2)

#define CAPSLOCK (1 << 3)
#define NUMLOCK (1 << 4)
#define SCROLLLOCK (1 << 5)

#define E0ESC (1 << 6)

static uint8_t shiftcode[256] = {[0x1d] = CTL, [0x2a] = SHIFT, [0x36] = SHIFT,
                                 [0x38] = ALT, [0x9d] = CTL,   [0xb8] = ALT};

static uint8_t togglecode[256] = {[0x3a] = CAPSLOCK, [0x45] = NUMLOCK, [0x46] = SCROLLLOCK};

static uint8_t normalmap[256] = {NO,
                                 0x1b,
                                 '1',
                                 '2',
                                 '3',
                                 '4',
                                 '5',
                                 '6', /* 0x00 */
                                 '7',
                                 '8',
                                 '9',
                                 '0',
                                 '-',
                                 '=',
                                 '\b',
                                 '\t',
                                 'q',
                                 'w',
                                 'e',
                                 'r',
                                 't',
                                 'y',
                                 'u',
                                 'i', /* 0x10 */
                                 'o',
                                 'p',
                                 '[',
                                 ']',
                                 '\n',
                                 NO,
                                 'a',
                                 's',
                                 'd',
                                 'f',
                                 'g',
                                 'h',
                                 'j',
                                 'k',
                                 'l',
                                 ';', /* 0x20 */
                                 '\'',
                                 '`',
                                 NO,
                                 '\\',
                                 'z',
                                 'x',
                                 'c',
                                 'v',
                                 'b',
                                 'n',
                                 'm',
                                 ',',
                                 '.',
                                 '/',
                                 NO,
                                 '*', /* 0x30 */
                                 NO,
                                 ' ',
                                 NO,
                                 NO,
                                 NO,
                                 NO,
                                 NO,
                                 NO,
                                 NO,
                                 NO,
                                 NO,
                                 NO,
                                 NO,
                                 NO,
                                 NO,
                                 '7', /* 0x40 */
                                 '8',
                                 '9',
                                 '-',
                                 '4',
                                 '5',
                                 '6',
                                 '+',
                                 '1',
                                 '2',
                                 '3',
                                 '0',
                                 '.',
                                 NO,
                                 NO,
                                 NO,
                                 NO, /* 0x50 */
                                 [0xc7] = KEY_HOME,
                                 [0x9c] = '\n', /* KP_Enter */
                                 [0xb5] = '/' /*KP_Div*/,
                                 [0xc8] = KEY_UP,
                                 [0xc9] = KEY_PGUP,
                                 [0xcb] = KEY_LF,
                                 [0xcd] = KEY_RT,
                                 [0xcf] = KEY_END,
                                 [0xd0] = KEY_DN,
                                 [0xd1] = KEY_PGDN,
                                 [0xd2] = KEY_INS,
                                 [0xd3] = KEY_DEL};

static uint8_t shiftmap[256] = {NO,
                                033,
                                '!',
                                '@',
                                '#',
                                '$',
                                '%',
                                '^', /* 0x00 */
                                '&',
                                '*',
                                '(',
                                ')',
                                '_',
                                '+',
                                '\b',
                                '\t',
                                'Q',
                                'W',
                                'E',
                                'R',
                                'T',
                                'Y',
                                'U',
                                'I', /* 0x10 */
                                'O',
                                'P',
                                '{',
                                '}',
                                '\n',
                                NO,
                                'A',
                                'S',
                                'D',
                                'F',
                                'G',
                                'H',
                                'J',
                                'K',
                                'L',
                                ':', /* 0x20 */
                                '"',
                                '~',
                                NO,
                                '|',
                                'Z',
                                'X',
                                'C',
                                'V',
                                'B',
                                'N',
                                'M',
                                '<',
                                '>',
                                '?',
                                NO,
                                '*', /* 0x30 */
                                NO,
                                ' ',
                                NO,
                                NO,
                                NO,
                                NO,
                                NO,
                                NO,
                                NO,
                                NO,
                                NO,
                                NO,
                                NO,
                                NO,
                                NO,
                                '7', /* 0x40 */
                                '8',
                                '9',
                                '-',
                                '4',
                                '5',
                                '6',
                                '+',
                                '1',
                                '2',
                                '3',
                                '0',
                                '.',
                                NO,
                                NO,
                                NO,
                                NO, /* 0x50 */
                                [0xc7] = KEY_HOME,
                                [0x9c] = '\n' /* KP_Enter */,
                                [0xb5] = '/' /*KP_Div*/,
                                [0xc8] = KEY_UP,
                                [0xc9] = KEY_PGUP,
                                [0xcb] = KEY_LF,
                                [0xcd] = KEY_RT,
                                [0xcf] = KEY_END,
                                [0xd0] = KEY_DN,
                                [0xd1] = KEY_PGDN,
                                [0xd2] = KEY_INS,
                                [0xd3] = KEY_DEL};

#define C(x) (x - '@')

static uint8_t ctlmap[256] = {NO,
                              NO,
                              NO,
                              NO,
                              NO,
                              NO,
                              NO,
                              NO,
                              NO,
                              NO,
                              NO,
                              NO,
                              NO,
                              NO,
                              NO,
                              NO,
                              C('Q'),
                              C('W'),
                              C('E'),
                              C('R'),
                              C('T'),
                              C('Y'),
                              C('U'),
                              C('I'),
                              C('O'),
                              C('P'),
                              NO,
                              NO,
                              '\r',
                              NO,
                              C('A'),
                              C('S'),
                              C('D'),
                              C('F'),
                              C('G'),
                              C('H'),
                              C('J'),
                              C('K'),
                              C('L'),
                              NO,
                              NO,
                              NO,
                              NO,
                              C('\\'),
                              C('Z'),
                              C('X'),
                              C('C'),
                              C('V'),
                              C('B'),
                              C('N'),
                              C('M'),
                              NO,
                              NO,
                              C('/'),
                              NO,
                              NO,
                              [0x97] = KEY_HOME,
                              [0xb5] = C('/'),
                              [0xc8] = KEY_UP,
                              [0xc9] = KEY_PGUP,
                              [0xcb] = KEY_LF,
                              [0xcd] = KEY_RT,
                              [0xcf] = KEY_END,
                              [0xd0] = KEY_DN,
                              [0xd1] = KEY_PGDN,
                              [0xd2] = KEY_INS,
                              [0xd3] = KEY_DEL};

static uint8_t *charcode[4] = {normalmap, shiftmap, ctlmap, ctlmap};

/*
 * Get data from the keyboard.  If we finish a character, return it.  Else 0.
 * Return -1 if no data.
 */
static int kbd_getc(void *arg)
{
    int c;
    uint8_t stat, data;
    static uint32_t shift;

    stat = inb(KBSTATP);
    if ((stat & KBS_DIB) == 0)
        return -1;
    /* ignore data from mouse */
    if (stat & KBS_TERR)
        return -1;

    data = inb(KBDATAP);

    if (data == 0xe0) {
        /* E0 escape character */
        shift |= E0ESC;
        return 0;
    } else if (data & 0x80) {
        /* key released */
        data = (shift & E0ESC ? data : data & 0x7f);
        shift &= ~(shiftcode[data] | E0ESC);
        return 0;
    } else if (shift & E0ESC) {
        /* last character was an E0 escape; or with 0x80 */
        data |= 0x80;
        shift &= ~E0ESC;
    }

    shift |= shiftcode[data];
    shift ^= togglecode[data];

    c = charcode[shift & (CTL | SHIFT)][data];
    if (shift & CAPSLOCK) {
        if ('a' <= c && c <= 'z')
            c += 'A' - 'a';
        else if ('A' <= c && c <= 'Z')
            c += 'a' - 'A';
    }

    return c;
}

void kbd_init(void)
{
    static struct console_device dev = {.getc = kbd_getc};

    console_register(&dev);
}
