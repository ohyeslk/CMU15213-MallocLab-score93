/*
 * mm.c
 * Implementing findfit then  coalesce and then find fit. 
 * experiment with first fit/best fit 
 *
 * Coalescing on evey block 
 * First Fit
 * Inline Functions
 * #######PERFECT
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <limits.h>
#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUGx
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
 
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)


/*
 * If NEXT_FIT defined use next fit search, else use first fit search 
 */
/*#define NEXT_FIT*/
#define FIRST_FIT
// #define BEST_FIT

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ //line:vm:mm:beginconst
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<9)  /* Extend heap by this amount (bytes) */  //line:vm:mm:endconst 

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))   
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //line:vm:mm:ftrp

/* Given block ptr bp from heap, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* From free_list */
#define GET_NEXTP(bp)            (*(void **)(bp + DSIZE))
#define GET_PREVP(bp)            (*(void **)bp)
#define SET_NEXTP(bp, ptr)       (GET_NEXTP(bp) = ptr)
#define SET_PREVP(bp, ptr)       (GET_PREVP(bp) = ptr)





/* $end mallocmacros */

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */  
static char *free_listp = 0;  /* Pointer to root free block */  
#ifdef NEXT_FIT
    static char *rover;           /* Next fit rover */
#endif


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))



/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(size_t size);
static void printblock(void *bp); 
static void checkheap(int verbose);
static void checkblock(void *bp);
static void print_all();
static void print_free();
static void print_free_block(void *bp) ;
static void *add_free_list_lifo(void *bp);
static void print_free_block(void *bp) ;
static void delete_free_list(void *bp);
static void add_free_list(void *bp);
static void *coalesce_block(void *bp) ;
/*
 *
 *Change of complete algo.
 * Rough Draft
 * free list -> free_listp
 * heap -> heap_listp
 * Coalesce in the end- when no new block left(will avoid several bugs)
 *     i.e. free_list == NULL
 *      even better, coalesce only till the point u get free memory of the
 *      required size.
 * Add New Block, put padding etc.-- add as free.
 *
 * Free Block : Add to free list, add pointers in it
 *
 * Allocating from free_list, delete from list, and then allocate.
 *     Splice the block if needed
 **/


/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    dbg_printf("mm_init in");
    /*Initialize global variables*/
    heap_listp = NULL;
    free_listp = NULL;
    /* Create the initial empty heap */

    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) 
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);                     
    #ifdef NEXT_FIT
        rover = heap_listp;
    #endif
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        dbg_printf("Error Mm_init\n");
        return -1;
    }
    dbg_printf("mm_init out \n");
    return 0;
}
/* $end mminit */



/*
 * malloc
 */
void *malloc (size_t size) {
    dbg_printf("--------------Start Malloc for size : %li ---------------\n", size);    
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      
    //dbg_printf("-------Malloc for size = %lu \n", size);
    /*if((int)size == 17 ){
        print_all();
        dbg_printf("----------\n");
        print_free();
        return NULL;
    }*/
    if (heap_listp == 0){
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
       return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE) { 
        asize = 4*DSIZE;
    } else {
        /*add overhead and align */
        asize = ALIGN( DSIZE + size )  ;      
    }
    /* Search the free list for a fit */
    /*As coalesce implicitly does Best Fit search, we can remove this iteration*/
    if ((bp = find_fit(asize)) != NULL) { 
        place(bp, asize);                 
        return bp;
    }

    // dbg_printf("Passed free list\n");
    /* No fit found. Coalesce*/
    /*Coalesce will return a pointer to free block ,if it fits(first fit only)*/
    /*Not needed now. Coalescing block wise*/
    /*    if( (bp = coalesce(asize)) != NULL) {
        Voila , we have found a free block
        place(bp, asize);                 
        return bp;
    }*/
    /*Still here, we need to extend the heap*/
    extendsize = MAX(asize,CHUNKSIZE);                 
    // dbg_printf("extendsize = %lu, CHUNKSIZE = %d\n", extendsize , CHUNKSIZE);  
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;                         //line:vm:mm:growheap2
    place(bp, asize);                       //line:vm:mm:growheap3
    return bp;
}

/* 
 * mm_free - Free a block 
 */

void mm_free(void *bp)
{
    dbg_printf("-----------------Start Free for Block: %p -------- \n", bp);
    if(bp == 0) 
       return;
    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0){
       mm_init();
    }
    /* Convert to Explicit list -- Implement LIFO*/
    //  printblock(bp);
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    /*Coalesce the block before adding to free list*/
    // coalesce_block(bp);
    bp = add_free_list_lifo(bp);
    /*Coalesce on freeing the memory*/
    
    dbg_printf("mm_free out");
}
/*
 * coalesce - Block wise. Need to be done after every block free.
 */
static inline void *coalesce_block(void *bp) 
{
    dbg_printf("Coalesce Block in\n");
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    //print_free();
    if (prev_alloc && next_alloc) {            /* Case 1 */
        //dbg_printf("case 1");
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        //dbg_printf("case 2");
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        /*Next is not allocated-- remove from free list*/
        delete_free_list(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
        /*add_free_list_lifo(bp);*/

    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        //dbg_printf("case 3");
        bp = PREV_BLKP(bp);
        size += GET_SIZE(HDRP(bp));
        /*Previous is not allocated-- remove from free list*/
        delete_free_list(bp);
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
                /*add_free_list_lifo(bp);*/
        /*PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));*/
    }

    else {                                     /* Case 4 */
        //dbg_printf("case 4");
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        delete_free_list(PREV_BLKP(bp));
        delete_free_list(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    dbg_printf("coalesce block out\n");
    //print_all();
    return bp;
    //return  NULL;
}

/*
 * coalesce - whole list
 */
static void *coalesce(size_t size) 
{
    dbg_printf("coalesce in");
    //dbg_printf("-- Free List Before Coalesce, for size:%lu \n",size);
    //print_free();
    if(free_listp == NULL)
        return NULL;
    void *bp= free_listp;
    void *next = GET_NEXTP(bp);
    void *temploc = NULL;
    unsigned int temploc_size = INT_MAX;
    size_t new_size;
    /*Not needed now*/
    /*new_size = GET_SIZE(HDRP(bp));
    dbg_printf( "new_size1 = %lu\n", new_size);
    if( size <= GET_SIZE(HDRP(bp))) {
        dbg_printf("Returning size %u\n",GET_SIZE(HDRP(bp)) );
        return bp;
    }*/
    
    while( next != NULL )
    {
        /*Iterate through free list, and coalesce adjacent free 
            blocks*/
        /* Following code not needed in new algo */
        /*if( size < GET_SIZE(HDRP(bp)) ) {
            dbg_printf("Returning size %u\n",GET_SIZE(HDRP(bp)) );
            return bp;
        }*/
        if( NEXT_BLKP(bp) == next ) {

            //Its adjacent free nodes
            /*new_size = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(next));*/
            delete_free_list(next);
            delete_free_list(bp);
            new_size = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(next));
            //dbg_printf("new_size3 = %lu\n",new_size );
            PUT(HDRP(bp), PACK(new_size, 0));
            PUT(FTRP(bp), PACK(new_size, 0));
            bp = add_free_list_lifo(bp);
            if( size != 0 && size < new_size  && temploc_size > new_size) {
                temploc = bp;
                temploc_size = size;
            }

        } 
        bp = next;
        next = GET_NEXTP(bp);

    }
    size = 1;
    if(size == 0){
        checkheap(0);    
    }
    
    //dbg_printf("-- Free List After Coalesce: \n");
    //print_free();
    dbg_printf("coalesce out");
    return temploc;
    //return  NULL;
}

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static inline void *extend_heap(size_t words) 
{
    dbg_printf("In extend_heap \n");
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    //dbg_printf("extend_heap, size = %lu\n", size);    
    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    bp = add_free_list_lifo(bp);
    dbg_printf("extend_heap out");
    return bp;
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */

static inline void place(void *bp, size_t asize)
{
    dbg_printf("place in \n");
    size_t csize = GET_SIZE(HDRP(bp));  
    //print_free_block(bp) ;
    delete_free_list(bp);
    //dbg_printf("csize : %lu ; asize : %lu \n", csize, asize);
    if ((csize - asize) >= (4*DSIZE)) { 
        /*Minimum size to be left for free list is 4*DSIZE=32*/
        //dbg_printf("Place Case 1\n");
        PUT(HDRP(bp), PACK(asize, 1));
        //dbg_printf("Line 409\n");
        PUT(FTRP(bp), PACK(asize, 1));
        //dbg_printf("Line 409\n");
        /* Splice the Next Block */
        bp = NEXT_BLKP(bp);
        //dbg_printf("place case 1, l3\n");
        PUT(HDRP(bp), PACK(csize-asize, 0));
        //dbg_printf("place case 1, l4\n");
        PUT(FTRP(bp), PACK(csize-asize, 0));
        //dbg_printf("place case 1, l5\n");
        /*Add the newly spliced block to free list*/
        bp = add_free_list_lifo(bp);
    }
    else { 
        //dbg_printf("place case 2\n");
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    //checkheap(1);
    dbg_printf("place out \n");
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static inline void *find_fit(size_t asize)
{
       dbg_printf("find_fit in \n");
    #ifdef NEXT_FIT 
        /* Next fit search */
        char *oldrover = rover;

        /* Search from the rover to the end of list */
        for ( ; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
            if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover)))) {
                return rover;
            }
            

        /* search from start of list to old rover */
        for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover)))) {
            return rover;
        }
            

        return NULL;  /* no fit found */
    #elif defined BEST_FIT
        if (free_listp == NULL) {
            return NULL;
        }
        /* Best fit search */
        void *bp = free_listp;
        void *temploc;
        temploc = NULL;
        unsigned int temploc_size=INT_MAX;
        unsigned int curr_size=INT_MAX;
        for (bp = free_listp; (bp!=NULL) 
          && (curr_size = GET_SIZE(HDRP(bp))) > 0;) {
            if( !GET_ALLOC(HDRP(bp)) && ( asize <= curr_size ) &&
             temploc_size >  curr_size ) {
                temploc = bp;
                temploc_size = curr_size;
            }
            bp = GET_NEXTP(bp);
        }    
        return temploc;
    #else
        /* First fit search */
        void *bp;
        for (bp = free_listp; (bp!=NULL) && GET_SIZE(HDRP(bp)) > 0; bp = GET_NEXTP(bp)) {
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                //print_free();
                return bp;

            }
        }
        return NULL; /* No fit */
    #endif
}


static void checkblock(void *bp) 
{
    if ((size_t)bp % 8) {
       dbg_printf("Error: %p is not doubleword aligned\n", bp);
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp))) {
        dbg_printf("Error: header does not match footer\n");
        dbg_printf("**Debug Info \n");
        dbg_printf("Heap_listp = %p \n", heap_listp );
        dbg_printf("Block %p \n", bp );
    }        
}

/* 
 * checkheap - Minimal check of the heap for consistency 
 */

/* Checks:
 * 1. if blocks are aligned.
 * 1. if it is in the heap.
 * 2. if the list is aligned.
 * 3. Print the address of that block.
 * 4. Print the previous and next free block.
 * 5. Get next block in free list.
 * 6. Print # of blocks in linked list.
 * 7. Check for the cycle in the list.
 */
void checkheap(int verbose) 
{
    //printf("check heap in \n");
    char *bp = heap_listp;

    if(verbose ==10) {
        print_all();
        print_free();
        print_free_block(free_listp);
        bp = find_fit(10);
        add_free_list(free_listp);
        add_free_list_lifo(free_listp);
        coalesce(0);
    }
    if (verbose){
        dbg_printf("Heap (%p):\n", heap_listp);        
    }

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))){
        printf("Bad prologue header\n");
    }
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) 
            printblock(bp);
            checkblock(bp);

    }

    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
        printf("Bad epilogue header for block \n");
        printblock(bp);
    }
    /* Check for count of free blocks, iterating over blocks and by 
     * going through next pointers*/
    unsigned int counti = 0;
    unsigned int countp = 0;
    /*Iterate over list*/   
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if(!GET_ALLOC(HDRP(bp))) {
            counti++;
        }
    }
    /* Moving free list by pointers*/
    for (bp = free_listp; (bp!=NULL) 
      &&  (GET_SIZE(HDRP(bp)) > 0);bp = GET_NEXTP(bp)) {
        countp++;
    }   
    if(countp!=counti) {
        printf("Error, No. of free block mismatch\n");
        dbg_printf("free\n");
        print_free();
        dbg_printf("all\n");
        print_all();
    }
    /*Check for cycle in the free list*/
    void *hare= free_listp;
    void *tortoise = free_listp;

    while( tortoise != NULL && hare != NULL  ) {
        if( hare !=  NULL ) {
            hare = GET_NEXTP(hare);
        }
        if( hare != NULL ) {
            tortoise = GET_NEXTP(hare);
        }
        
        dbg_printf("Check cycle\n"); 
        if( hare == tortoise ){
            /*Its a cycle .. error . */
            printf("There is a cycle in the free_list\n");       
        }
    }
    dbg_printf("checkheap out \n");
}

/*
 * print_all() - Prints every block in the heap structure
 */
void print_all()
{
    dbg_printf("All Blocks :\n ");
    void *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
           printblock(bp);
    }
}

/*
 * print_free() - Prints all the free memory, in order
 */
void print_free()
{
    dbg_printf("Free Blocks :\n ");
    void *bp = free_listp;
    while(bp != NULL && GET_SIZE(HDRP(bp)) > 0)
    {       
        printblock(bp);
        bp = GET_NEXTP(bp);
    }
    //dbg_printf("Free Blocks done :\n ");
}


static void printblock(void *bp) 
{   
    size_t hsize=-1, halloc, fsize, falloc;
    if ( bp != NULL) {
        hsize = GET_SIZE(HDRP(bp));
        halloc = GET_ALLOC(HDRP(bp));  
        fsize = GET_SIZE(FTRP(bp));
        falloc = GET_ALLOC(FTRP(bp));  
        dbg_printf("%p: header: [%lu:%c] footer: [%lu:%c]\n", bp,\
            hsize, (halloc ? 'a' : 'f'), \
            fsize, (falloc ? 'a' : 'f')); 
    } else {
        dbg_printf("bp is NULL\n");
    }
    if (hsize == 0) {
        dbg_printf("%p: EOL\n", bp);
    return;
    }
}

static void print_free_block(void *bp) 
{
    dbg_printf("Printing free block for ptr %p\n", bp);
    size_t hsize = -1, halloc, fsize, falloc;

    // checkheap(0);
    if(bp != NULL) {
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    dbg_printf("%p: header: [%lu:%c] footer: [%lu:%c]\n", bp,hsize, \
        (halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f')); 
    dbg_printf( "%p: next: [%p] prev: [%p]\n  ", bp, GET_NEXTP(bp), \
        GET_PREVP(bp) );
    } else {
        dbg_printf("bp is null\n");
    }
    if (hsize == 0) {
        dbg_printf("%p: EOL\n", bp);
    return;
    }

}


static void add_free_list(void *bp){
    dbg_printf("add_free_list in \n");
    /*Add free list, ordered by addres*/
    void * cur;
    /*Hanadle corner case*/
    if (free_listp == NULL){ 
        SET_PREVP(bp, NULL);
        SET_NEXTP(bp, NULL);
        free_listp = bp;
    } 

    /*Search for correct location and insert*/
    else if(free_listp != NULL) {
        cur = free_listp;
        for (cur = free_listp; (cur!=NULL) && cur < bp; bp = GET_NEXTP(bp)) {
            /*Do the manipulation, inset before current*/        
            SET_NEXTP( bp, cur );
            SET_PREVP( bp, GET_PREVP(cur) );
            if( GET_PREVP(cur) != NULL ) {
                SET_NEXTP( GET_PREVP(cur), bp );
            }
            SET_PREVP( cur , bp  );
        }
    }
    dbg_printf("add_free_list out \n");
}


/* Add - add the specific block ptr to the free list,
* making it the first element in the list . Implementing using 
* LIFO Strategy
* */
static void *add_free_list_lifo(void *bp)
{
    dbg_printf("add_free_list_lifo in \n");
    /*Add the free node at the head 
     *    Root now points to new free block. Next of new free block 
     *   points to the previous root block
     */
    
    /*Coalesce the block*/
    bp = coalesce_block(bp);
    /*print_free();
    dbg_printf("Block Bp after coalesce\n");
    printblock(bp);
    print_free();
    print_all();
    dbg_printf("add to list");*/
    if (free_listp == NULL){ 
        SET_PREVP(bp, NULL);
        SET_NEXTP(bp, NULL);
    } else if(free_listp != NULL) {
        SET_NEXTP(bp, free_listp);
        SET_PREVP(bp, NULL);
        SET_PREVP( free_listp, bp  );
    }
    /*Point next of bp to where root node was pointing*/
    /*Make root to point to new node*/
    free_listp = bp;
    /*Coalesce every time u add to free list*/
    /*print_free();
    print_all();
    dbg_printf("Goto Check heap \n");*/
    //checkheap(1);
    dbg_printf("add_free_list_lifo out \n");
    return bp;
}

/*Delete a block from the free list.-- eq. to allocating memory */
static  inline void delete_free_list(void *bp)
{
    dbg_printf("delete_free_list in \n");
    void *next = GET_NEXTP(bp);
    void *prev = GET_PREVP(bp);
    /*Handle corner case of deleting head node.*/
    if(bp == free_listp){
        free_listp = next;
    }
    if(prev != NULL) {
        SET_NEXTP(prev, next);
    }
    if(next != NULL) {
        SET_PREVP(next, prev);
    }

    /*Clean Up task. Set next/prev pointers of bp to NULL*/
    SET_NEXTP(bp,NULL);
    SET_PREVP(bp,NULL);
    dbg_printf("delete_free_list out \n");
    /*Probably should mark it to allocated too..have to decide*/
}

/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) {
        /*Get gcc to be quiet. */
     verbose = verbose;
}
/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) 
{
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

/*
 * mm_realloc - Naive implementation of realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    dbg_printf("--------------Start Re-Malloc for size : %li ---------------\n", size);    
    size_t oldsize;
    void *newptr;
    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(ptr);
        return 0;
    }
    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return mm_malloc(size);
    }
    newptr = mm_malloc(size);
    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }
    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize)
         oldsize = size;
    memcpy(newptr, ptr, oldsize);
    /* Free the old block. */
    mm_free(ptr);
    return newptr;
}