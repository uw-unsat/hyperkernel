#if ENABLED(CONFIG_NVME)

#include <uapi/machine/cpufunc.h>
#include <uapi/machine/mmu.h>
#include <uapi/nvme.h>
#include <uapi/pcireg.h>
#include "fs.h"
#include "uiommu.h"

#define BLKSECTS (BSIZE / 512)

/* queue sizes */
#define ADMINQ_SIZE 8
#define IOQ_SIZE 8

struct nvme_queue {
    uint16_t id;
    size_t size;

    /* submission queue */
    void *sq_va;
    void *sq_tdbl;
    uint32_t sq_tail;

    /* completion queue */
    void *cq_va;
    void *cq_hdbl;
    uint32_t cq_head;
    uint16_t cq_phase;
};

/* queues */
static struct nvme_queue adminq, ioq;

static uint8_t adminq_sq[PAGE_SIZE] __aligned(PAGE_SIZE);
static uint8_t adminq_cq[PAGE_SIZE] __aligned(PAGE_SIZE);
static uint8_t ioq_sq[PAGE_SIZE] __aligned(PAGE_SIZE);
static uint8_t ioq_cq[PAGE_SIZE] __aligned(PAGE_SIZE);
static uint8_t data_buf[PAGE_SIZE] __aligned(PAGE_SIZE);

static void nvme_queue_init(struct nvme_queue *q, void *sq, void *cq, void *base, uint16_t id,
                            size_t size, size_t dstrd)
{
    memset(q, 0, sizeof(*q));
    q->id = id;
    q->size = size;

    q->sq_va = sq;
    q->sq_tdbl = base + NVME_SQTDBL(id, dstrd);

    q->cq_va = cq;
    q->cq_hdbl = base + NVME_CQHDBL(id, dstrd);
}

static int nvme_queue_submit(struct nvme_queue *q, void *cmd)
{
    struct nvme_sqe *sqe = q->sq_va;
    volatile struct nvme_cqe *cqe = q->cq_va;

    sqe += q->sq_tail;
    cqe += q->cq_head;

    /* copy to SQ */
    memcpy(sqe, cmd, sizeof(struct nvme_sqe));

    /* bump the SQ tail pointer */
    ++q->sq_tail;
    if (q->sq_tail == q->size)
        q->sq_tail = 0;

    /* ring the SQ doorbell */
    mmio_write32(q->sq_tdbl, q->sq_tail);

    /* wait for CQ */
    while ((cqe->flags & NVME_CQE_PHASE) == q->cq_phase)
        ;
    assert(NVME_CQE_SC(cqe->flags) == NVME_CQE_SC_SUCCESS, "cq must succeed");

    /* bump the CQ head pointer */
    ++q->cq_head;
    if (q->cq_head == q->size) {
        q->cq_head = 0;
        q->cq_phase ^= NVME_CQE_PHASE;
    }

    /* ring the CQ doorbell */
    mmio_write32(q->cq_hdbl, q->cq_head);

    return 0;
}

static void nvme_queue_create(struct nvme_queue *q)
{
    struct nvme_sqe_q cmd_add_iocq = {
        .opcode = NVM_ADMIN_ADD_IOCQ,
        .prp1 = (uintptr_t)q->cq_va,
        .qsize = q->size - 1,
        .qid = q->id,
        .qflags = NVM_SQE_Q_PC,
    };
    struct nvme_sqe_q cmd_add_iosq = {
        .opcode = NVM_ADMIN_ADD_IOSQ,
        .prp1 = (uintptr_t)q->sq_va,
        .qsize = q->size - 1,
        .qid = q->id,
        .cqid = q->id,
        .qflags = NVM_SQE_Q_PC,
    };

    static_assert(sizeof(struct nvme_sqe_q) == sizeof(struct nvme_sqe), "sqe size match");
    /* create CQ */
    nvme_queue_submit(&adminq, &cmd_add_iocq);
    /* create SQ */
    nvme_queue_submit(&adminq, &cmd_add_iosq);
}

static size_t find_pci(void)
{
    size_t i;

    for (i = 0; i < NPCIDEV; ++i) {
        if (udevs[i].class != PCI_CLASS_MASS_STORAGE)
            continue;
        if (udevs[i].subclass != PCI_SUBCLASS_MASS_STORAGE_NVM)
            continue;
        if (udevs[i].interface != PCI_INTERFACE_NVM_NVME)
            continue;
        break;
    }
    if (i == NPCIDEV)
        panic("fs: nvme not found");

    return i;
}

void unix_init(void)
{
    pn_t root;
    void *base;
    uint32_t cc, dstrd;
    uint64_t cap;

    pr_info("fs: use NVMe\n");

    /* BAR 0: NVMe base address */
    root = iommu_alloc_root(find_pci(), UPCI_START, 0);
    base = (void *)(uintptr_t)UPCI_START;

    iommu_map(root, adminq_sq, sizeof(adminq_sq));
    iommu_map(root, adminq_cq, sizeof(adminq_cq));
    iommu_map(root, ioq_sq, sizeof(ioq_sq));
    iommu_map(root, ioq_cq, sizeof(ioq_cq));
    iommu_map(root, data_buf, sizeof(data_buf));

    cap = mmio_read64(base + NVME_CAP);
    assert(NVME_CAP_MPSMIN(cap) <= PAGE_SHIFT, "cap mpsmin");
    assert(NVME_CAP_MPSMAX(cap) >= PAGE_SHIFT, "cap mpsmax");
    dstrd = NVME_CAP_DSTRD(cap);

    cc = mmio_read32(base + NVME_CC);
    assert(!(cc & NVME_CC_EN), "not enabled");

    nvme_queue_init(&adminq, adminq_sq, adminq_cq, base, NVME_ADMIN_Q, ADMINQ_SIZE, dstrd);
    /* set admin queue sizes */
    mmio_write32(base + NVME_AQA, NVME_AQA_ACQS(ADMINQ_SIZE) | NVME_AQA_ASQS(ADMINQ_SIZE));
    /* set admin queue addresses */
    mmio_write64(base + NVME_ACQ, (uintptr_t)adminq.cq_va);
    mmio_write64(base + NVME_ASQ, (uintptr_t)adminq.sq_va);

    /* set control configuration */
    cc &= ~(NVME_CC_IOCQES_MASK | NVME_CC_IOSQES_MASK | NVME_CC_AMS_MASK | NVME_CC_MPS_MASK |
            NVME_CC_CSS_MASK);
    cc |= NVME_CC_IOSQES(__builtin_ffs(64) - 1) | NVME_CC_IOCQES(__builtin_ffs(16) - 1);
    cc |= NVME_CC_AMS(NVME_CC_AMS_RR);
    cc |= NVME_CC_MPS(PAGE_SHIFT);
    cc |= NVME_CC_CSS(NVME_CC_CSS_NVM);
    cc |= NVME_CC_EN;
    mmio_write32(base + NVME_CC, cc);

    /* wait until the controller is ready */
    while (!(mmio_read32(base + NVME_CSTS) & NVME_CSTS_RDY))
        pause();

    /* create I/O queues */
    nvme_queue_init(&ioq, ioq_sq, ioq_cq, base, 1, IOQ_SIZE, dstrd);
    nvme_queue_create(&ioq);
}

void unix_read(uint64_t block, void *buf)
{
    struct nvme_sqe_io cmd = {
        .opcode = NVM_CMD_READ,
        .nsid = 1,
        .slba = block * BLKSECTS,
        .nlb = BLKSECTS - 1,
        .entry.prp[0] = (uintptr_t)data_buf,
    };

    nvme_queue_submit(&ioq, &cmd);
    memcpy(buf, data_buf, BSIZE);
}

void unix_write(uint64_t block, const void *buf)
{
    struct nvme_sqe_io cmd = {
        .opcode = NVM_CMD_WRITE,
        .nsid = 1,
        .slba = block * BLKSECTS,
        .nlb = BLKSECTS - 1,
        .entry.prp[0] = (uintptr_t)data_buf,
    };

    memcpy(data_buf, buf, BSIZE);
    nvme_queue_submit(&ioq, &cmd);
}

void unix_flush(void)
{
}

#endif /* CONFIG_NVME */
