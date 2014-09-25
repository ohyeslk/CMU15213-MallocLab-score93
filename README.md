CMU15213-MallocLab-score93
==========================
Uploaded at Aug 23, 2014

Algorithm: I have created segregated list, stored on heap, to keep track of all the free nodes. As soon as a block is freed, it is put on the free list and coalesced if needed. When allocating, free list are checked for first fit block starting from correct seg list for the size and iterating over other lists. If no free node found, memory is extended by chunk size.
