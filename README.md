# Malloc-Lab
Malloc Package produced by Ann Zhang.

This memory allocator is based on segregated free lists.

The smallest block class on the free list is 16 bytes in size, with a header, a footer and the pointer to its successor.

There exist free blocks of 8 bytes, owning a header and a footer each, but such blocks can't be found on the free list and are exclusively taken into account when coalescing.

Every block has a header. However, only a free block has a footer. Whether the preceding block is allocated is recorded in the second lowest bit of the header.
