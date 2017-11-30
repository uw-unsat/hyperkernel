#pragma once

#include <uapi/cdefs.h>

/* Registers */
#define E1000_CTRL 0x00000  /* Device Control - RW */
#define E1000_STATUS 0x00008 /* Device Status - RO */
#define E1000_EECD 0x00010   /* EEPROM/Flash Control - RW */
#define E1000_EERD 0x00014   /* EEPROM Read - RW */
#define E1000_ICR 0x000c0    /* Interrupt Cause Read - R/clr */
#define E1000_ITR 0x000c4    /* Interrupt Throttling Rate - RW */
#define E1000_ICS 0x000c8    /* Interrupt Cause Set - WO */
#define E1000_IMS 0x000d0    /* Interrupt Mask Set - RW */
#define E1000_EIAC 0x000dc   /* Ext. Interrupt Auto Clear - RW */
#define E1000_IMC 0x000d8    /* Interrupt Mask Clear - WO */
#define E1000_IAM 0x000e0    /* Interrupt Acknowledge Auto Mask */
#define E1000_IVAR 0x000e4   /* Interrupt Vector Allocation Register - RW */
#define E1000_EITR 0x000e8   /* Extended Interrupt Throttling Rate - RW */
#define E1000_RCTL 0x00100   /* RX Control - RW */
#define E1000_TCTL 0x00400   /* TX Control - RW */
#define E1000_TIPG 0x00410   /* TX Inter-packet gap -RW */
#define E1000_RDBAL 0x02800  /* RX Descriptor Base Address Low - RW */
#define E1000_RDBAH 0x02804  /* RX Descriptor Base Address High - RW */
#define E1000_RDH 0x02810    /* RX Descriptor Head - RW */
#define E1000_RDT 0x02818    /* RX Descriptor Tail - RW */
#define E1000_RDLEN 0x02808  /* RX Descriptor Length - RW */
#define E1000_TDBAL 0x03800  /* TX Descriptor Base Address Low - RW */
#define E1000_TDBAH 0x03804  /* TX Descriptor Base Address High - RW */
#define E1000_TDLEN 0x03808  /* TX Descriptor Length - RW */
#define E1000_TDH 0x03810    /* TX Descriptor Head - RW */
#define E1000_TDT 0x03818    /* TX Descripotr Tail - RW */
#define E1000_MTA 0x05200    /* Multicast Table Array - RW Array */
#define E1000_RAL 0x05400     /* Receive Address Low - RW Array */
#define E1000_RAH 0x05404     /* Receive Address High - RW Array */

#define E1000_RAH_AV 0x80000000

/* Device Control */
#define E1000_CTRL_SLU      0x00000040  /* Set link up (Force Link) */
#define E1000_CTRL_FRCSPD   0x00000800  /* Force Speed */
#define E1000_CTRL_FRCDPX   0x00001000  /* Force Duplex */
#define E1000_CTRL_RST      0x04000000  /* Global reset */
#define E1000_CTRL_PHY_RST  0x80000000  /* PHY Reset */

/* Device Status */
#define E1000_STATUS_FD         0x00000001      /* Full duplex.0=half,1=full */
#define E1000_STATUS_LU         0x00000002      /* Link up.0=no,1=link */
#define E1000_STATUS_FUNC_MASK  0x0000000C      /* PCI Function Mask */
#define E1000_STATUS_FUNC_SHIFT 2
#define E1000_STATUS_FUNC_0     0x00000000      /* Function 0 */
#define E1000_STATUS_FUNC_1     0x00000004      /* Function 1 */
#define E1000_STATUS_TXOFF      0x00000010      /* transmission paused */
#define E1000_STATUS_TBIMODE    0x00000020      /* TBI mode */
#define E1000_STATUS_SPEED_MASK 0x000000C0
#define E1000_STATUS_SPEED_10   0x00000000      /* Speed 10Mb/s */
#define E1000_STATUS_SPEED_100  0x00000040      /* Speed 100Mb/s */
#define E1000_STATUS_SPEED_1000 0x00000080      /* Speed 1000Mb/s */

/* Interrupt Cause Read */
#define E1000_ICR_TXDW 0x00000001   /* Transmit desc written back */
#define E1000_ICR_TXQE 0x00000002   /* Transmit Queue empty */
#define E1000_ICR_LSC 0x00000004    /* Link Status Change */
#define E1000_ICR_RXSEQ 0x00000008  /* rx sequence error */
#define E1000_ICR_RXDMT0 0x00000010 /* rx desc min. threshold (0) */
#define E1000_ICR_RXO 0x00000040    /* rx overrun */
#define E1000_ICR_RXT0 0x00000080   /* rx timer intr (ring 0) */

/* Transmit Control */
#define E1000_TCTL_RST 0x00000001 /* software reset */
#define E1000_TCTL_EN 0x00000002  /* enable tx */
#define E1000_TCTL_BCE 0x00000004 /* busy check enable */
#define E1000_TCTL_PSP 0x00000008 /* pad short packets */
#define E1000_TCTL_CT 0x00000ff0  /* collision threshold */
#define E1000_TCTL_CT_SHIFT 4
#define E1000_TCTL_COLD 0x003ff000 /* collision distance */
#define E1000_TCTL_COLD_SHIFT 12
#define E1000_TCTL_SWXOFF 0x00400000 /* SW Xoff transmission */
#define E1000_TCTL_PBE 0x00800000    /* Packet Burst Enable */
#define E1000_TCTL_RTLC 0x01000000   /* Re-transmit on late collision */
#define E1000_TCTL_NRTU 0x02000000   /* No Re-transmit on underrun */
#define E1000_TCTL_MULR 0x10000000   /* Multiple request support */

/* Receive Control */
#define E1000_RCTL_RST 0x00000001         /* Software reset */
#define E1000_RCTL_EN 0x00000002          /* enable */
#define E1000_RCTL_SBP 0x00000004         /* store bad packet */
#define E1000_RCTL_UPE 0x00000008         /* unicast promiscuous enable */
#define E1000_RCTL_MPE 0x00000010         /* multicast promiscuous enab */
#define E1000_RCTL_LPE 0x00000020         /* long packet enable */
#define E1000_RCTL_LBM_NO 0x00000000      /* no loopback mode */
#define E1000_RCTL_LBM_MAC 0x00000040     /* MAC loopback mode */
#define E1000_RCTL_LBM_SLP 0x00000080     /* serial link loopback mode */
#define E1000_RCTL_LBM_TCVR 0x000000C0    /* tcvr loopback mode */
#define E1000_RCTL_DTYP_MASK 0x00000C00   /* Descriptor type mask */
#define E1000_RCTL_DTYP_PS 0x00000400     /* Packet Split descriptor */
#define E1000_RCTL_RDMTS_HALF 0x00000000  /* rx desc min threshold size */
#define E1000_RCTL_RDMTS_QUAT 0x00000100  /* rx desc min threshold size */
#define E1000_RCTL_RDMTS_EIGTH 0x00000200 /* rx desc min threshold size */
#define E1000_RCTL_MO_SHIFT 12            /* multicast offset shift */
#define E1000_RCTL_MO_0 0x00000000        /* multicast offset 11:0 */
#define E1000_RCTL_MO_1 0x00001000        /* multicast offset 12:1 */
#define E1000_RCTL_MO_2 0x00002000        /* multicast offset 13:2 */
#define E1000_RCTL_MO_3 0x00003000        /* multicast offset 15:4 */
#define E1000_RCTL_MDR 0x00004000         /* multicast desc ring 0 */
#define E1000_RCTL_BAM 0x00008000         /* broadcast enable */
/* these buffer sizes are valid if E1000_RCTL_BSEX is 0 */
#define E1000_RCTL_SZ_2048 0x00000000 /* rx buffer size 2048 */
#define E1000_RCTL_SZ_1024 0x00010000 /* rx buffer size 1024 */
#define E1000_RCTL_SZ_512 0x00020000  /* rx buffer size 512 */
#define E1000_RCTL_SZ_256 0x00030000  /* rx buffer size 256 */
/* these buffer sizes are valid if E1000_RCTL_BSEX is 1 */
#define E1000_RCTL_SZ_16384 0x00010000    /* rx buffer size 16384 */
#define E1000_RCTL_SZ_8192 0x00020000     /* rx buffer size 8192 */
#define E1000_RCTL_SZ_4096 0x00030000     /* rx buffer size 4096 */
#define E1000_RCTL_VFE 0x00040000         /* vlan filter enable */
#define E1000_RCTL_CFIEN 0x00080000       /* canonical form enable */
#define E1000_RCTL_CFI 0x00100000         /* canonical form indicator */
#define E1000_RCTL_DPF 0x00400000         /* discard pause frames */
#define E1000_RCTL_PMCF 0x00800000        /* pass MAC control frames */
#define E1000_RCTL_BSEX 0x02000000        /* Buffer size extension */
#define E1000_RCTL_SECRC 0x04000000       /* Strip Ethernet CRC */
#define E1000_RCTL_FLXBUF_MASK 0x78000000 /* Flexible buffer size */
#define E1000_RCTL_FLXBUF_SHIFT 27        /* Flexible buffer shift */

/* Transmit Descriptor bit definitions */
#define E1000_TXD_CMD_EOP    0x01000000 /* End of Packet */
#define E1000_TXD_CMD_IFCS   0x02000000 /* Insert FCS (Ethernet CRC) */
#define E1000_TXD_CMD_RS     0x08000000 /* Report Status */
#define E1000_TXD_STAT_DD    0x00000001 /* Descriptor Done */

/* Receive Descriptor bit definitions [E1000 3.2.3.1] */
#define E1000_RXD_STAT_DD 0x01  /* Descriptor Done */
#define E1000_RXD_STAT_EOP 0x02 /* End of Packet */

/* EEPROM/Flash Control */
#define E1000_EECD_REQ 0x00000040 /* EEPROM Access Request */
#define E1000_EECD_GNT 0x00000080 /* EEPROM Access Grant */

#define E1000_EERD_DATA_MASK 0xffff0000

#define EEPROM_OFF_MACADDR 0x00 /* MAC address offset */

/* Transmit Descriptor */
struct e1000_tx_desc {
    uint64_t buffer_addr;       /* Address of the descriptor's data buffer */
    union {
        uint32_t data;
        struct {
            uint16_t length;    /* Data buffer length */
            uint8_t cso;        /* Checksum offset */
            uint8_t cmd;        /* Descriptor control */
        } flags;
    } lower;
    union {
        uint32_t data;
        struct {
            uint8_t status;     /* Descriptor status */
            uint8_t css;        /* Checksum start */
            uint16_t special;
        } fields;
    } upper;
} __packed;

/* Legacy Receive Descriptor */
struct e1000_rx_desc {
    uint64_t buffer_addr; /* Address of the descriptor's data buffer */
    uint16_t length;     /* Length of data DMAed into data buffer */
    uint16_t csum;       /* Packet checksum */
    uint8_t status;      /* Descriptor status */
    uint8_t errors;      /* Descriptor Errors */
    uint16_t special;
} __packed;
