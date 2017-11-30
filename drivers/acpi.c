#include <acpi.h>
#include <bootmem.h>
#include <string.h>

#define ACPI_MAX_TABLE_COUNT 32
#define ACPI_COMPARE_NAME(a, b) (memcmp(a, b, sizeof(uint32_t)) == 0)

struct acpi_tables {
    struct acpi_table_header *tables[ACPI_MAX_TABLE_COUNT];
    uint32_t count;
};

static struct acpi_tables acpi_tables;

static void print_table_rsdp(struct acpi_table_rsdp *rsdp)
{
    pr_info("acpi: RSDP 0x%016" PRIX64 " %06X (v%.2d %.6s)\n", kva2pa(rsdp),
            (rsdp->revision) ? rsdp->length : 20, rsdp->revision, rsdp->oem_id);
}

static void print_table_header(struct acpi_table_header *hdr)
{
    pr_info("acpi: %.4s 0x%016" PRIX64 " %06X (v%.2d %.6s %.8s %08X %.4s %08X)\n", hdr->signature,
            kva2pa(hdr), hdr->length, hdr->revision, hdr->oem_id, hdr->oem_table_id,
            hdr->oem_revision, hdr->asl_compiler_id, hdr->asl_compiler_revision);
}

static uint8_t sum(void *addr, int len)
{
    int i, sum;

    sum = 0;
    for (i = 0; i < len; i++)
        sum += ((uint8_t *)addr)[i];
    return sum;
}

/* Look for the RSDP in the len bytes at physical address addr. */
static struct acpi_table_rsdp *rsdp_search1(physaddr_t a, int len)
{
    void *p = pa2kva(a), *e = pa2kva(a + len);

    /* The signature is on a 16-byte boundary. */
    for (; p < e; p += 16) {
        struct acpi_table_rsdp *rsdp = p;

        if (memcmp(rsdp->signature, ACPI_SIG_RSDP, 8) || sum(rsdp, 20))
            continue;
        /* ACPI 2.0+ */
        if (rsdp->revision && sum(rsdp, rsdp->length))
            continue;
        return rsdp;
    }
    return NULL;
}

/* Search for the RSDP at the following locations: */
/* * the first KB of the EBDA; */
/* the BIOS ROM between 0xe0000 and 0xfffff. */
static struct acpi_table_rsdp *rsdp_search(void)
{
    physaddr_t ebda;
    struct acpi_table_rsdp *rsdp;

    /* The 16-bit segment of the EBDA is in the two byte at 0x40:0x0e. */
    ebda = *(uint16_t *)pa2kva(0x40e);
    ebda <<= 4;
    rsdp = rsdp_search1(ebda, 1024);
    if (rsdp)
        return rsdp;
    return rsdp_search1(0xe0000, 0x20000);
}

void acpi_init(void)
{
    struct acpi_table_rsdp *rsdp = NULL;
    struct acpi_table_header *hdr;
    const char *sig;
    size_t entry_size;
    void *p, *e;
    uint32_t i;

    if (!rsdp) {
        rsdp = rsdp_search();
        if (!rsdp)
            panic("acpi: no RSDP found in EBDA");
    }
    print_table_rsdp(rsdp);

    if (rsdp->revision) {
        hdr = pa2kva(rsdp->xsdt_physical_address);
        sig = ACPI_SIG_XSDT;
        entry_size = 8;
    } else {
        hdr = pa2kva(rsdp->rsdt_physical_address);
        sig = ACPI_SIG_RSDT;
        entry_size = 4;
    }

    if (memcmp(hdr->signature, sig, 4))
        panic("acpi: incorrect %s signature", sig);
    if (sum(hdr, hdr->length))
        panic("acpi: bad %s checksum", sig);
    print_table_header(hdr);

    p = hdr + 1;
    e = (void *)hdr + hdr->length;
    for (i = 0; p < e; p += entry_size) {
        hdr = pa2kva(*(uint32_t *)p);
        if (sum(hdr, hdr->length))
            continue;
        print_table_header(hdr);
        assert(i < ACPI_MAX_TABLE_COUNT, "too many ACPI tables");
        acpi_tables.tables[i++] = hdr;
    }
    acpi_tables.count = i;
}

acpi_status acpi_get_table(char *signature, uint32_t instance, struct acpi_table_header **out_table)
{
    uint32_t i = 0, j = 0;

    for (; i < acpi_tables.count; ++i) {
        if (!ACPI_COMPARE_NAME(acpi_tables.tables[i]->signature, signature))
            continue;

        if (++j < instance)
            continue;

        *out_table = acpi_tables.tables[i];
        return AE_OK;
    }

    return AE_NOT_FOUND;
}
