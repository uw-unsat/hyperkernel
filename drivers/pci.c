#include <uapi/machine/cpufunc.h>
#include <uapi/machine/io.h>
#include <uapi/pci.h>
#include <uapi/pcireg.h>
#include <acpi.h>

/* non-zero: PCIe; otherwise PCI */
physaddr_t pci_config_base;

void (*pci_register_func)(struct pci_func *);

static SLIST_HEAD(pci_driver_list, pci_driver) drivers;

static int pci_match(struct pci_func *f)
{
    struct pci_driver *driver;

    SLIST_FOREACH(driver, &drivers, link)
    {
        if (driver->vendor != PCI_ANY_ID && driver->vendor != f->vendor)
            continue;
        if (driver->product != PCI_ANY_ID && driver->product != f->product)
            continue;
        if (driver->class != PCI_ANY_ID && driver->class != f->class)
            continue;
        if (driver->subclass != PCI_ANY_ID && driver->subclass != f->subclass)
            continue;
        if (driver->interface != PCI_ANY_ID && driver->interface != f->interface)
            continue;
        return 1;
    }
    return 0;
}

static const char *pci_class[] = {
        [PCI_CLASS_PREHISTORIC] = "prehistoric",
        [PCI_CLASS_MASS_STORAGE] = "mass storage",
        [PCI_CLASS_NETWORK] = "network",
        [PCI_CLASS_DISPLAY] = "display",
        [PCI_CLASS_MULTIMEDIA] = "multimedia",
        [PCI_CLASS_MEMORY] = "memory",
        [PCI_CLASS_BRIDGE] = "bridge",
        [PCI_CLASS_COMMUNICATIONS] = "communications",
        [PCI_CLASS_SYSTEM] = "system",
        [PCI_CLASS_INPUT] = "input",
        [PCI_CLASS_DOCK] = "dock",
        [PCI_CLASS_PROCESSOR] = "processor",
        [PCI_CLASS_SERIALBUS] = "serial bus",
        [PCI_CLASS_WIRELESS] = "wireless",
        [PCI_CLASS_I2O] = "I2O",
        [PCI_CLASS_SATCOM] = "satellite comm",
        [PCI_CLASS_CRYPTO] = "crypto",
        [PCI_CLASS_DASP] = "DASP",
};

static void pci_print_func(struct pci_func *f)
{
    const char *desc = NULL;

    if (f->class < countof(pci_class))
        desc = pci_class[f->class];
    if (!desc)
        desc = "Unknown";

    pr_info("pci: %02x:%02x.%d %04x:%04x %02x.%02x.%02x %s\n",
            pci_bus_num(f->devid), pci_dev_num(f->devid), pci_func_num(f->devid),
            f->vendor, f->product, f->class, f->subclass, f->interface, desc);
}

static void scan_pci_func(uint16_t devid)
{
    struct pci_func f = { .devid = devid };
    uint32_t v, bar, bar_width;

    v = pci_conf_read(devid, PCI_ID_REG);
    f.vendor = PCI_VENDOR(v);
    f.product = PCI_PRODUCT(v);
    if (f.vendor == 0xffff)
        return;

    v = pci_conf_read(devid, PCI_CLASS_REG);
    f.class = PCI_CLASS(v);
    f.subclass = PCI_SUBCLASS(v);
    f.interface = PCI_INTERFACE(v);
    f.revision = PCI_REVISION(v);

    pci_print_func(&f);

    if (!pci_match(&f))
        return;

    pci_conf_write(devid, PCI_COMMAND_STATUS_REG,
        PCI_COMMAND_IO_ENABLE | PCI_COMMAND_MEM_ENABLE | PCI_COMMAND_MASTER_ENABLE);

    for (bar = PCI_MAPREG_START; bar < PCI_MAPREG_END; bar += bar_width) {
        uint32_t oldv, rv;
        int regnum;
        uint64_t base, size;
        const char *type;

        bar_width = 4;
        oldv = pci_conf_read(devid, bar);
        pci_conf_write(devid, bar, 0xffffffff);
        rv = pci_conf_read(devid, bar);

        if (rv == 0)
            continue;

        regnum = PCI_MAPREG_NUM(bar);
        if (PCI_MAPREG_TYPE(rv) == PCI_MAPREG_TYPE_MEM) {
            if (PCI_MAPREG_MEM_TYPE(rv) == PCI_MAPREG_MEM_TYPE_64BIT) {
                uint32_t oldv64h, rv64h;

                bar_width = 8;
                oldv64h = pci_conf_read(devid, bar + 4);
                pci_conf_write(devid, bar + 4, 0xffffffff);
                rv64h = pci_conf_read(devid, bar + 4);
                pci_conf_write(devid, bar + 4, oldv64h);
                size = PCI_MAPREG_MEM64_SIZE(((uint64_t)rv64h << 32) | rv);
                base = PCI_MAPREG_MEM64_ADDR(((uint64_t)oldv64h << 32) | oldv);
            } else {
                size = PCI_MAPREG_MEM_SIZE(rv);
                base = PCI_MAPREG_MEM_ADDR(oldv);
            }
            type = "mem";
        } else {
            size = PCI_MAPREG_IO_SIZE(rv);
            base = PCI_MAPREG_IO_ADDR(oldv);
            type = "io ";
        }

        pr_info("pci:   BAR %d [%s 0x%04" PRIx64 "-0x%04" PRIx64 "]\n",
                regnum, type, base, base + size - 1);

        pci_conf_write(devid, bar, oldv);
        f.reg_base[regnum] = base;
        f.reg_size[regnum] = size;
    }

    if (pci_register_func)
        pci_register_func(&f);
}

void pci_init(void)
{
    acpi_status status;
    struct acpi_table_mcfg *mcfg;
    int bus = 0, lastbus = 255, dev, func;

    status = acpi_get_table(ACPI_SIG_MCFG, 0, (struct acpi_table_header **)&mcfg);
    if (ACPI_SUCCESS(status)) {
        struct acpi_mcfg_baa *hdr, *end;

        hdr = (void *)mcfg + sizeof(struct acpi_table_mcfg);
        end = (void *)mcfg + mcfg->header.length;
        for (; hdr < end; ++hdr) {
            pr_info("pci: base address 0x%08" PRIx64 " segment 0x%04x [bus 0x%02x-0x%02x]\n",
                    hdr->base_address, hdr->segment_group_no,
                    hdr->start_bus_no, hdr->end_bus_no);
            /* segment 0 only for now */
            if (hdr->segment_group_no == 0) {
                bus = hdr->start_bus_no;
                lastbus = hdr->end_bus_no;
                /*
                 * Adjust if bus doesn't start from 0.
                 *
                 * Since each function takes a page, each bus takes 256 (32 * 8) pages.
                 */
                pci_config_base = hdr->base_address - bus * 256 * SZ_4K;
                pr_info("pci: use Enhanced Configuration Access Mechanism\n");
            }
        }
    } else {
        pr_warn("pci: MCFG not found\n");
    }

    for (; bus <= lastbus; ++bus) {
        for (dev = 0; dev < 32; ++dev) {
            uint32_t bhlc;

            /* unsupported or no device */
            bhlc = pci_conf_read(pci_devid(bus, dev, 0), PCI_BHLC_REG);
            if (PCI_HDRTYPE_TYPE(bhlc) > 1)
                continue;

            for (func = 0; func < (PCI_HDRTYPE_MULTIFN(bhlc) ? 8 : 1); ++func)
                scan_pci_func(pci_devid(bus, dev, func));
        }
    }
}

void pci_register_driver(struct pci_driver *driver)
{
    SLIST_INSERT_HEAD(&drivers, driver, link);
}

/* PCI "configuration mechanism one" */

static void pci_conf1_set_addr(uint16_t devid, uint32_t offset)
{
    assert(offset < 256, "offset must be valid");
    assert((offset & 0x3) == 0, "offset must be valid");

    uint32_t v = BIT32(31) | ((uint32_t)devid << 8) | offset;
    outl(PORT_PCI_CONF_ADDRESS, v);
}

uint32_t pci_conf_read(uint16_t devid, uint32_t off)
{
    if (pci_config_base)
        return mmio_read32(pa2kva(pci_config_addr(devid) + off));
    pci_conf1_set_addr(devid, off);
    return inl(PORT_PCI_CONF_DATA);
}

void pci_conf_write(uint16_t devid, uint32_t off, uint32_t v)
{
    if (pci_config_base)
        return mmio_write32(pa2kva(pci_config_addr(devid) + off), v);
    pci_conf1_set_addr(devid, off);
    outl(PORT_PCI_CONF_DATA, v);
}
