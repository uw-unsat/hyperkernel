#pragma once

#include <uapi/queue.h>

#define PCI_ANY_ID (~0U)

#define PCI_DRIVER_ID(vendor, product) \
    { vendor, product, PCI_ANY_ID, PCI_ANY_ID, PCI_ANY_ID }

#define PCI_DRIVER_CLASS(class, subclass, interface) \
    { PCI_ANY_ID, PCI_ANY_ID, class, subclass, interface }

struct pci_func {
    uint16_t devid;

    uint16_t vendor;
    uint16_t product;

    uint8_t class;
    uint8_t subclass;
    uint8_t interface;
    uint8_t revision;

    uint64_t reg_base[6];
    uint64_t reg_size[6];
};

/* PCI driver table */
struct pci_driver {
    uint32_t vendor, product;
    uint32_t class, subclass, interface;

    SLIST_ENTRY(pci_driver) link;
};

/* must be called before pci_init() */
void pci_register_driver(struct pci_driver *);

void pci_init(void);

uint32_t pci_conf_read(uint16_t devid, uint32_t off);
void pci_conf_write(uint16_t devid, uint32_t off, uint32_t v);

static inline uint16_t pci_devid(int bus, int dev, int func)
{
    return (bus << 8) | (dev << 3) | func;
}

static inline uint8_t pci_bus_num(uint16_t devid)
{
    return devid >> 8;
}

static inline uint8_t pci_dev_num(uint16_t devid)
{
    return (devid >> 3) & 0x1f;
}

static inline uint8_t pci_func_num(uint16_t devid)
{
    return devid & 0x07;
}

/* PCIe configuration base address */
extern physaddr_t pci_config_base;

static inline physaddr_t pci_config_addr(uint16_t devid)
{
    return pci_config_base + devid * SZ_4K;
}

/* OS callback */
extern void (*pci_register_func)(struct pci_func *);
