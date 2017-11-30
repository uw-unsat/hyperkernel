#pragma once

typedef uint32_t cptr_t;

enum {
    NUM_CONTAINER_CAPABILITY_SLOTS = 64,
};

enum cap_type {
    /* Capability slot is empty and carries no data. */
    CAP_TYPE_EMPTY = 0,
    /* Capability to another container */
    CAP_TYPE_CONTAINER,
    CAP_TYPE_ENV,
    CAP_TYPE_FRAME_1K,
    CAP_TYPE_FRAME_4K,
    CAP_TYPE_FRAME_1M,
    CAP_TYPE_FRAME_2M,
    CAP_TYPE_FRAME_4M,
    CAP_TYPE_FRAME_1G,
    CAP_TYPE_PAGEMAP_L0, /* Page Mapping Level 0 */
    CAP_TYPE_PAGEMAP_L1, /* Page Mapping Level 1 */
    CAP_TYPE_PAGEMAP_L2, /* Page Mapping Level 2 */
    CAP_TYPE_PAGEMAP_L3, /* Page Mapping Level 3 */
};
