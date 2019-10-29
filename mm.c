/*
 * This implementation replicates the implicit list implementation
 * provided in the textbook
 * "Computer Systems - A Programmer's Perspective"
 * Blocks are never coalesced or reused.
 * Realloc is implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "nyana",
    /* First member's full name */
    "Manukiran Kamath",
    /* First member's email address */
    "manukiran.kamath@mail.utoronto.ca",
    /* Second member's full name (do not modify this as this is an individual lab) */
    "",
    /* Second member's email address (do not modify this as this is an individual lab)*/
    ""
};

/*************************************************************************
 * Basic Constants and Macros
 * You are not required to use these macros but may find them helpful.
*************************************************************************/
#define WSIZE       sizeof(void *)            /* word size (bytes) */
#define DSIZE       (2 * WSIZE)            /* doubleword size (bytes) */
#define CHUNKSIZE   (1<<7)      /* initial heap size (bytes) */

#define MAX(x,y) ((x) > (y)?(x) :(y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)          (*(uintptr_t *)(p))
#define PUT(p,val)      (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)    (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/*************************************************************************
 * Custom Constants and Macros
*************************************************************************/
#define MAX_SIZE_CLASS 20 //experiment with this
#define MINIMUM_BLOCK_SIZE 32 //factoring in 16 bytes overhead and alignment

/*Global variables*/
void* heap_listp = NULL;
int request_id; //this is for debugging comment it out later
static void *segregated_list[MAX_SIZE_CLASS];

/*Forward declarations*/
size_t map_size_class (size_t size);
static void myprintblock(void *bp);
static void mycheckblock(void *bp);
static int check_overlap (void);
static int check_hf_consistency(void *bp);
static int check_aligment(void *bp);
static int check_no_uncoalesced_free_blocks(void *bp);
static void myheapcheck(void);
int mm_check(void);
void *extend_heap(size_t words);

/**********************************************************
* Function that maps a given size to a size class.  
* Corner case: if we get too big a size, need to handle this
* while adding a free block. 
**********************************************************/
size_t map_size_class (size_t size){
    size_t size_class = 0;
    while ((size >>= 1) != 0){
        size_class++;
    }
    return size_class;
}

/**********************************************************
* Function that places a free block in the appropriate free list
* of the seglist.
* Returns the new root ptr (the free block we just added) to the
* segregated list for that size class. 
* For now, LIFO (free block gets placed at the start of the list)
* Later address ordered. 
**********************************************************/
// void *add_free_block_to_list (void *free_bp, size_t size){

//     //block should not be a duplicate
//     //assert ()

//     //find appropriate size class

//     size_t size_class = map_size_class(size);
//     size_class = (size_class > MAX_SIZE_CLASS) ? MAX_SIZE_CLASS : size_class;

//     //get the current root of the list (this is just the appropriate ptr 
//     //in the segregated list)

//     void *current_root = segregated_list[size_class];

//     //now make our new free block the new root.
//     //this is pseudocode at this point, check again 

//     current_root->pred = free_bp;
//     free_bp->succ = current_root;
//     return free_bp;
// }

/**********************************************************
 * mm_init
 * Initialize the heap, including "allocation" of the
 * prologue and epilogue
 **********************************************************/
 // int mm_init(void)
 // {
 //    //check consistency

 //   if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
 //         return -1;
 //     PUT(heap_listp, 0);                         // alignment padding
 //     PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));   // prologue header
 //     PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));   // prologue footer
 //     PUT(heap_listp + (3 * WSIZE), PACK(0, 1));    // epilogue header
 //     heap_listp += DSIZE;

 //     //check consistency

 //     return 0;
 // }
  int mm_init(void)
 {
    request_id = -1; 
    char *bp;

    //check consistency

   if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
         return -1;
     PUT(heap_listp, 0);                         // alignment padding
     PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));   // prologue header
     PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));   // prologue footer
     PUT(heap_listp + (3 * WSIZE), PACK(0, 1));    // epilogue header
     heap_listp += DSIZE;

     // check consistency
     printf("before extend:\n");
     myheapcheck();

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
     if ((bp = extend_heap(4*CHUNKSIZE)) == NULL)
        return -1;

     printf("after extend:\n");
     myheapcheck();

     // exit(0); //for debugging purposes
     return 0;
 }

/**********************************************************
 * coalesce
 * Covers the 4 cases discussed in the text:
 * - both neighbours are allocated
 * - the next block is available for coalescing
 * - the previous block is available for coalescing
 * - both neighbours are available for coalescing
 **********************************************************/
void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {       /* Case 1 */
        return bp;
    }

    else if (prev_alloc && !next_alloc) { /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        return (bp);
    }

    else if (!prev_alloc && next_alloc) { /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        return (PREV_BLKP(bp));
    }

    else {            /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))  +
            GET_SIZE(FTRP(NEXT_BLKP(bp)))  ;
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        return (PREV_BLKP(bp));
    }
}

/**********************************************************
 * extend_heap
 * Extend the heap by "words" words, maintaining alignment
 * requirements of course. Free the former epilogue block
 * and reallocate its new header
 **********************************************************/
void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignments */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ( (bp = mem_sbrk(size)) == (void *)-1 )
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));                // free block header
    PUT(FTRP(bp), PACK(size, 0));                // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));        // new epilogue header

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}


/**********************************************************
 * find_fit
 * Traverse the heap searching for a block to fit asize
 * Return NULL if no free blocks can handle that size
 * Assumed that asize is aligned
 **********************************************************/
void * find_fit(size_t asize)
{
    void *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            return bp;
        }
    }
    return NULL;
}

/**********************************************************
 * place
 * Mark the block as allocated
 **********************************************************/
void place(void* bp, size_t asize)
{
  /* Get the current block size */
  size_t bsize = GET_SIZE(HDRP(bp));
  assert(bsize >= asize); //should be allocating to a suitably big free block 
  size_t split_size = bsize - asize;

  if (split_size <= MINIMUM_BLOCK_SIZE){
    //don't split in this case
    PUT(HDRP(bp), PACK(bsize, 1)); 
    PUT(FTRP(bp), PACK(bsize, 1));
  }

  else {
    //Split block
    PUT(FTRP(bp), PACK(split_size, 0)); //old ftrp becomes ftrp of split free block
    PUT(HDRP(bp), PACK(asize, 1)); //old hdrp becomes hdrp of split alloced block
    PUT(FTRP(bp), PACK(asize, 1)); //get the new footer of the newly alloced block
    PUT(HDRP(NEXT_BLKP(bp)), PACK(split_size, 0)); //set the new hdrp for the split free block
  }

  // for debugging purposes
  // if (request_id == 3)
  //   exit(0);
  request_id++;
}

/**********************************************************
 * mm_free
 * Free the block and coalesce with neighbouring blocks
 **********************************************************/
void mm_free(void *bp)
{
    // printf("Before free(%p):\n",bp);
    // myheapcheck();

    if(bp == NULL){
      return;
    }
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    coalesce(bp); //currently we coalesce in any case. are there times we don't wanna coalesce?
    //segregated/explicit list free - address ordered, free list blocks must be in 
    //addr(pred) < addr(curr) < addr(succ)
    printf("After free(%p):\n",bp);
    myheapcheck();
}


/**********************************************************
 * mm_malloc
 * Allocate a block of size bytes.
 * The type of search is determined by find_fit
 * The decision of splitting the block, or not is determined
 *   in place(..)
 * If no block satisfies the request, the heap is extended
 **********************************************************/
void *mm_malloc(size_t size)
{
    size_t asize; /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char * bp;

    // printf("Before malloc(%zu):\n",size);
    // myheapcheck();

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/ DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        printf("After malloc(%zu): malloc(%zu)\n", size, asize);
        myheapcheck();
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    printf("After malloc(%zu): malloc(%zu)\n", size, asize);
    myheapcheck();
    return bp;

}

/**********************************************************
 * mm_realloc
 * Implemented simply in terms of mm_malloc and mm_free
 *********************************************************/
void *mm_realloc(void *ptr, size_t size)
{
    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0){
      mm_free(ptr);
      return NULL;
    }
    /* If oldptr is NULL, then this is just malloc. */
    if (ptr == NULL)
      return (mm_malloc(size));

    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;

    /* Copy the old data. */
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

/**********************************************************
 * mm_check
 * Check the consistency of the memory heap
 * Return nonzero if the heap is consistent.
 *
 * Consistency Checks include:
 * 1) Is every block in the free list marked as free?
 * 2) Are there any contiguous free blocks that escaped
 *    coalescing?
 * 3) Are all blocks marked as free in the heap added
 *    to the segregated list?
 * 4) Do all blocks hashing to a certain index in the 
 *    hash table fit within the correct size class of the
 *    segregated free list?
 *    
 *********************************************************/
static void myprintblock(void *bp){
    volatile size_t hdr_alloc = GET_ALLOC(HDRP(bp));
    volatile size_t hdr_size = GET_SIZE(HDRP(bp));
    volatile char alloc_h = hdr_alloc ? 'a' : 'f';

    volatile size_t ftr_alloc = GET_ALLOC(FTRP(bp));
    volatile size_t ftr_size = GET_SIZE(FTRP(bp));
    volatile char alloc_f = ftr_alloc ? 'a' : 'f';

    size_t payload_size = hdr_alloc ? hdr_size - DSIZE : 0;
    if (alloc_h == 'a'){
        printf("a: header: [%zu,%c,%d,%zu] footer: [%zu,%c]\n", hdr_size, alloc_h, request_id, payload_size, ftr_size, alloc_f);
    }
    if (alloc_h == 'f'){
        printf("f: header: [%zu,%c] footer: [%zu,%c]\n", hdr_size, alloc_h, ftr_size, alloc_f);
    }
}

/**********************************************************
 * Checks that free blocks have been coalesced. 
 * Corner cases: start and end of heap
 *********************************************************/
static int check_no_uncoalesced_free_blocks(void *bp){

    size_t bp_alloc = GET_ALLOC(HDRP(bp));
    size_t next_bp_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));    
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t prev_bp_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));

    unsigned int prev_blk_free = (prev_bp_size != 0) && (prev_alloc == 0);
    unsigned int next_blk_free = (next_bp_size != 0) && (next_alloc == 0);

    //corner cases
    if (bp_alloc == 0){
        if (prev_blk_free || next_blk_free){
            fprintf(stderr, "mm_check: uncoalesced free blocks!\n");
            assert (0);
        }
    }
    return 1; 
} 
/**********************************************************
 * Checks header-footer consistency & alignment.
 * Return non-zero if pass.
 *********************************************************/
static int check_hf_consistency(void *bp){
    volatile size_t hdr_size = GET_SIZE(HDRP(bp));
    volatile size_t hdr_alloc = GET_ALLOC(HDRP(bp));
    volatile size_t ftr_size = GET_SIZE(FTRP(bp));
    volatile size_t ftr_alloc = GET_ALLOC(FTRP(bp));
    //check header consistency
    if (hdr_size != ftr_size || hdr_alloc != ftr_alloc){
        fprintf(stderr, "mm_check: header-footer consistency failed!\n");
        assert(0); //failed header-footer consistency check
    }    
    return 1;
}

static int check_aligment(void *bp){
    assert(check_hf_consistency(bp)); //no metadata incosistency
    if (!((size_t)HDRP(bp) % DSIZE) || !((size_t)HDRP(NEXT_BLKP(bp)) % DSIZE)) {
        fprintf(stderr, "mm_check: alignment test failed!\n");
        assert(0);
    }
    return 1; 
}

// static int check_overlap (){

// }

/**********************************************************
 * Neanderthal mm_check.
 *********************************************************/
static void mycheckblock(void *bp){
    volatile size_t hdr_size = GET_SIZE(HDRP(bp));
    volatile size_t hdr_alloc = GET_ALLOC(HDRP(bp));
    volatile size_t ftr_size = GET_SIZE(FTRP(bp));
    volatile size_t ftr_alloc = GET_ALLOC(FTRP(bp));
    //check header consistency
    if (hdr_size != ftr_size || hdr_alloc != ftr_alloc){
        fprintf(stderr, "my_check: header-footer consistency failed!\n");
        assert(0); //failed header-footer consistency check
    }
    //check if aligned
    if (!((size_t)HDRP(bp) % DSIZE) || !((size_t)HDRP(NEXT_BLKP(bp)) % DSIZE)) {
        fprintf(stderr, "my_check: alignment test failed!\n");
        assert(0);
    }
    return;
}

static void myheapcheck(void){
    char *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        myprintblock(bp);
        // mycheckblock(bp);
        check_hf_consistency(bp);
        check_aligment(bp);
        check_no_uncoalesced_free_blocks(bp);
    }
    printf("my_check: pass\n");    
}

int mm_check(void){
  return 1;
}

