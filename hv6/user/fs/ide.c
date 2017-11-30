#include "fs.h"

void iderw(struct buf *b)
{
    if (!(b->flags & B_BUSY))
        panic("iderw: buf not busy");
    if ((b->flags & (B_VALID | B_DIRTY)) == B_VALID)
        panic("iderw: nothing to do");

    if (b->flags & B_DIRTY) {
        unix_write(b->sector, b->data);
        b->flags &= ~B_DIRTY;
    } else {
        unix_read(b->sector, b->data);
        b->flags |= B_VALID;
    }
}

void ideflush()
{
    unix_flush();
}
