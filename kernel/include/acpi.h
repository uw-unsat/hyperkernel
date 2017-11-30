#pragma once

#include <uapi/cdefs.h>

/* error code */

#define ACPI_SUCCESS(a) (!(a))
#define ACPI_FAILURE(a) (a)

#define AE_OK ((acpi_status)0x0000)

#define AE_CODE_ENVIRONMENTAL 0x0000 /* General ACPICA environment */
#define AE_CODE_PROGRAMMER 0x1000    /* External ACPICA interface caller */
#define AE_CODE_ACPI_TABLES 0x2000   /* ACPI tables */
#define AE_CODE_AML 0x3000           /* From executing AML code */
#define AE_CODE_CONTROL 0x4000       /* Internal control codes */

#define AE_CODE_MAX 0x4000
#define AE_CODE_MASK 0xF000

#define EXCEP_ENV(code) ((acpi_status)(code | AE_CODE_ENVIRONMENTAL))
#define EXCEP_PGM(code) ((acpi_status)(code | AE_CODE_PROGRAMMER))
#define EXCEP_TBL(code) ((acpi_status)(code | AE_CODE_ACPI_TABLES))
#define EXCEP_AML(code) ((acpi_status)(code | AE_CODE_AML))
#define EXCEP_CTL(code) ((acpi_status)(code | AE_CODE_CONTROL))

#define AE_NOT_FOUND EXCEP_ENV(0x0005)

/* headers */
#define ACPI_SIG_RSDP "RSD PTR "
#define ACPI_SIG_RSDT "RSDT"
#define ACPI_SIG_XSDT "XSDT"
#define ACPI_SIG_FADT "FACP"
#define ACPI_SIG_HPET "HPET"
#define ACPI_SIG_MADT "APIC"
#define ACPI_SIG_MCFG "MCFG"
#define ACPI_SIG_DMAR "DMAR"
#define ACPI_SIG_IVRS "IVRS"

#define ACPI_MADT_TYPE_LOCAL_APIC 0
#define ACPI_MADT_TYPE_LOCAL_X2APIC 9

#define ACPI_DMAR_TYPE_HARDWARE_UNIT 0

#define ACPI_IVRS_TYPE_HARDWARE 0x10

typedef uint32_t acpi_status;

struct acpi_generic_address {
    uint8_t space_id;     /* Address space where struct or register exists */
    uint8_t bit_width;    /* Size in bits of given register */
    uint8_t bit_offset;   /* Bit offset within the register */
    uint8_t access_width; /* Minimum Access size (ACPI 3.0) */
    uint64_t address;     /* 64-bit address of struct or register */
} __packed;

/* 5.2.5 Root System Description Pointer (RSDP) */
struct acpi_table_rsdp {
    uint8_t signature[8]; /* "RSD PTR " */
    uint8_t checksum;     /* first 20 bytes must add up to 0 */
    uint8_t oem_id[6];
    uint8_t revision;
    uint32_t rsdt_physical_address; /* 32-bit physical address of RSDT */
    uint32_t length;                /* table length */
    uint64_t xsdt_physical_address; /* 64-bit physical address of XSDT */
    uint8_t extended_checksum;      /* the entire table must add up to 0 */
    uint8_t reserved[3];
} __packed;

/* 5.2.6 System Description Table Header */
struct acpi_table_header {
    uint8_t signature[4]; /* "XSDT" */
    uint32_t length;      /* table length */
    uint8_t revision;
    uint8_t checksum; /* the entire table must add up to 0 */
    uint8_t oem_id[6];
    uint8_t oem_table_id[8];
    uint32_t oem_revision;
    uint8_t asl_compiler_id[4];
    uint32_t asl_compiler_revision;
} __packed;

/* 5.2.7 Root System Description Table (RSDT) */
struct acpi_table_rsdt {
    struct acpi_table_header header;
    uint32_t table_offset_entry[];
} __packed;

/* 5.2.8 Extended System Description Table (XSDT) */
struct acpi_table_xsdt {
    struct acpi_table_header header;
    uint64_t table_offset_entry[];
} __packed;

/* FADT - Fixed ACPI Description Table */
struct acpi_table_fadt {
    struct acpi_table_header header; /* Common ACPI table header */
    uint32_t facs;                   /* 32-bit physical address of FACS */
    uint32_t dsdt;                   /* 32-bit physical address of DSDT */
    uint8_t model;                   /* System Interrupt Model (ACPI 1.0) - not used in ACPI 2.0+ */
    uint8_t preferred_profile;       /* Conveys preferred power management profile to OSPM. */
    uint16_t sci_interrupt;          /* System vector of SCI interrupt */
    uint32_t smi_command;            /* 32-bit Port address of SMI command port */
    uint8_t acpi_enable;             /* Value to write to SMI_CMD to enable ACPI */
    uint8_t acpi_disable;            /* Value to write to SMI_CMD to disable ACPI */
    uint8_t s4_bios_request;         /* Value to write to SMI_CMD to enter S4BIOS state */
    uint8_t pstate_control;          /* Processor performance state control*/
    uint32_t pm1a_event_block;       /* 32-bit port address of Power Mgt 1a Event Reg Blk */
    uint32_t pm1b_event_block;       /* 32-bit port address of Power Mgt 1b Event Reg Blk */
    uint32_t pm1a_control_block;     /* 32-bit port address of Power Mgt 1a Control Reg Blk */
    uint32_t pm1b_control_block;     /* 32-bit port address of Power Mgt 1b Control Reg Blk */
    uint32_t pm2_control_block;      /* 32-bit port address of Power Mgt 2 Control Reg Blk */
    uint32_t pm_timer_block;         /* 32-bit port address of Power Mgt Timer Ctrl Reg Blk */
    uint32_t gpe0_block;             /* 32-bit port address of General Purpose Event 0 Reg Blk */
    uint32_t gpe1_block;             /* 32-bit port address of General Purpose Event 1 Reg Blk */
    uint8_t pm1_event_length;        /* Byte Length of ports at pm1x_event_block */
    uint8_t pm1_control_length;      /* Byte Length of ports at pm1x_control_block */
    uint8_t pm2_control_length;      /* Byte Length of ports at pm2_control_block */
    uint8_t pm_timer_length;         /* Byte Length of ports at pm_timer_block */
    uint8_t gpe0_block_length;       /* Byte Length of ports at gpe0_block */
    uint8_t gpe1_block_length;       /* Byte Length of ports at gpe1_block */
    uint8_t gpe1_base;               /* Offset in GPE number space where GPE1 events start */
    uint8_t cst_control;   /* Support for the _CST object and C-States change notification */
    uint16_t c2_latency;   /* Worst case HW latency to enter/exit C2 state */
    uint16_t c3_latency;   /* Worst case HW latency to enter/exit C3 state */
    uint16_t flush_size;   /* Processor memory cache line width, in bytes */
    uint16_t flush_stride; /* Number of flush strides that need to be read */
    uint8_t duty_offset;   /* Processor duty cycle index in processor P_CNT reg */
    uint8_t duty_width;    /* Processor duty cycle value bit width in P_CNT register */
    uint8_t day_alarm;     /* Index to day-of-month alarm in RTC CMOS RAM */
    uint8_t month_alarm;   /* Index to month-of-year alarm in RTC CMOS RAM */
    uint8_t century;       /* Index to century in RTC CMOS RAM */
    uint16_t boot_flags;   /* IA-PC Boot Architecture Flags (see below for individual flags) */
    uint8_t reserved;      /* Reserved, must be zero */
    uint32_t flags;        /* Miscellaneous flag bits (see below for individual flags) */
    struct acpi_generic_address reset_register; /* 64-bit address of the Reset register */
    uint8_t reset_value; /* Value to write to the reset_register port to reset the system */
    uint16_t
        arm_boot_flags; /* ARM-Specific Boot Flags (see below for individual flags) (ACPI 5.1) */
    uint8_t minor_revision; /* FADT Minor Revision (ACPI 5.1) */
    uint64_t Xfacs;         /* 64-bit physical address of FACS */
    uint64_t Xdsdt;         /* 64-bit physical address of DSDT */
    struct acpi_generic_address
        xpm1a_event_block; /* 64-bit Extended Power Mgt 1a Event Reg Blk address */
    struct acpi_generic_address
        xpm1b_event_block; /* 64-bit Extended Power Mgt 1b Event Reg Blk address */
    struct acpi_generic_address
        xpm1a_control_block; /* 64-bit Extended Power Mgt 1a Control Reg Blk address */
    struct acpi_generic_address
        xpm1b_control_block; /* 64-bit Extended Power Mgt 1b Control Reg Blk address */
    struct acpi_generic_address
        xpm2_control_block; /* 64-bit Extended Power Mgt 2 Control Reg Blk address */
    struct acpi_generic_address
        xpm_timer_block; /* 64-bit Extended Power Mgt Timer Ctrl Reg Blk address */
    struct acpi_generic_address
        xgpe0_block; /* 64-bit Extended General Purpose Event 0 Reg Blk address */
    struct acpi_generic_address
        xgpe1_block; /* 64-bit Extended General Purpose Event 1 Reg Blk address */
    struct acpi_generic_address sleep_control; /* 64-bit Sleep Control register (ACPI 5.0) */
    struct acpi_generic_address sleep_status;  /* 64-bit Sleep Status register (ACPI 5.0) */
    uint64_t hypervisor_id;                    /* Hypervisor Vendor ID (ACPI 6.0) */
} __packed;

/* HPET - High Precision Event Timer Table */
struct acpi_table_hpet {
    struct acpi_table_header header;     /* Common ACPI table header */
    uint32_t id;                         /* Hardware ID of event timer block */
    struct acpi_generic_address address; /* Address of event timer block */
    uint8_t sequence;                    /* HPET sequence number */
    uint16_t minimum_tick;               /* Main counter min tick, periodic mode */
    uint8_t flags;
} __packed;

struct acpi_table_madt {
    struct acpi_table_header header; /* Common ACPI table header */
    uint32_t address;                /* Physical address of local APIC */
    uint32_t flags;
} __packed;

struct acpi_subtable_header {
    uint8_t type;
    uint8_t length;
} __packed;

struct acpi_madt_local_apic {
    struct acpi_subtable_header header;
    uint8_t processor_id; /* ACPI processor id */
    uint8_t id;           /* Processor's local APIC id */
    uint32_t lapic_flags;
};

struct acpi_madt_local_x2apic {
    struct acpi_subtable_header header;
    uint16_t reserved;
    uint32_t local_apic_id; /* Processor's' x2APIC id */
    uint32_t lapic_flags;
    uint32_t uid; /* ACPI processor UID */
} __packed;

struct acpi_table_mcfg {
    struct acpi_table_header header;
    uint8_t reserved[8];
    /* contains subtables immediately following */
} __packed;

/* Base Address Allocations */
struct acpi_mcfg_baa {
    uint64_t base_address;
    uint16_t segment_group_no;
    uint8_t start_bus_no;
    uint8_t end_bus_no;
    uint32_t reserved;
} __packed;

/* DMA Remapping */
struct acpi_table_dmar {
    struct acpi_table_header header;
    uint8_t host_address_width;
    uint8_t flags;
    uint8_t reserved[10];
    /* contains subtables immediately following */
} __packed;

/* DMAR subtable header */
struct acpi_dmar_header {
    uint16_t type;
    uint16_t length;
} __packed;

/* ACPI_DMAR_TYPE_HARDWARE_UNIT */
struct acpi_dmar_hardware_unit {
    struct acpi_dmar_header header;
    uint8_t flags;
    uint8_t reserved;
    uint16_t segment;
    uint64_t address;
} __packed;

struct acpi_table_ivrs {
    struct acpi_table_header header;
    uint32_t info;
    uint64_t reserved;
} __packed;

/* IVRS subtable header */
struct acpi_ivrs_header {
    uint8_t type; /* subtable type */
    uint8_t flags;
    uint16_t length;    /* subtable length */
    uint16_t device_id; /* ID of IOMMU */
} __packed;

/* ACPI_IVRS_TYPE_HARDWARE */
struct acpi_ivrs_hardware {
    struct acpi_ivrs_header header;
    uint16_t capability_offset; /* offset for IOMMU control fields */
    uint64_t base_address;      /* IOMMU control registers */
    uint16_t pci_segment_group;
    uint16_t info; /* MSI number and unit ID */
    uint32_t reserved;
} __packed;

acpi_status acpi_get_table(char *signature, uint32_t instance,
                           struct acpi_table_header **out_table);
