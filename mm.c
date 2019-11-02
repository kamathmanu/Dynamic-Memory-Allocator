/*
 * HIGH LEVEL DESCRIPTION OF DESIGN:
 * A segregated list design that consists of various explicit free lists
 * of different size classes. Each nth size class is an explicit free list containing
 * free blocks of size (2^n * 32 + 1) bytes (which is the minimum size of a block after accounting
 * for alignment padding and overhead size) to (2^(n+1)*32)bytes. The exception is the
 * last size class (last bucket) which essentially doesn't have an upper limit for sizes.
 *
 * The segregated list (SL) is an array of 20 explicit free lists. Each element of the SL
 * points to the TAIL of the free list (this was done to make it easier to enforce LIFO policy).
 * As such one can traverse a given free list by getting the predecessor of the current block.
 *
 * Block Info and Metadata Tracking:
 * 
 * Allocated Blocks: These are similar to the implicit list version
 * Free blocks:
 * Header (8 bytes): Size (63 bits), Alloc (1 bit)
 * Pred* : calculated as Header + WSIZE
 * Succ* : Header + DSIZE
 * <unused> : Succ* + WSIZE gives the starting address of the free chunk/block.
 * Footer : same as header. 
 *
 * Allocation Policy:
 * I use a segregated-best fit approach to allocating requests. Based on the adjusted block
 * size to allocate, for asize S I search the appropriate free list [L,U] of size L <= S <= U
 * Then I traverse that linked list and search for a free block of size M >= S, and allocate the block.
 * After splitting the free block, we remove the remainder split block from that class if needed and
 * replace it in the appropriate size class. If no block is found, we try again in a bigger size
 * class. If even then, we don't find an adequate free block, we extend the heap by the minimum amount
 * needed. 
 * Allocation is linear to the # of free blocks. 
 *
 * Freeing policy:
 * I use a simple LIFO policy while freeing. This means if I have to insert a free block into
 * a free list, I simply make it the new tail node of the list. For removal, again it is constant
 * time and we simply reset the predecessor and successors. (TAs: if you are reading this and my
 * code is not using LIFO, I probably upgraded to address-ordered but forgot to update it here. I'll
 * really try not to though :( ))
 * Freeing is O(1).
 *
 * Coalescing Policy: Immediate coalescing without deferral. 
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
#define MIN(x,y) ((x) <= (y)?(x) :(y))
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))
/* Read and write a word at address p */
#define GET(p)          (*(uintptr_t *)(p))
#define PUT(p,val)      (*(uintptr_t *)(p) = (uintptr_t)(val))
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
#define PAGE_SIZE 4096
#define MAX_SIZE_CLASS 10 //experiment with this
#define MINIMUM_BLOCK_SIZE (2 * DSIZE) //factoring in 16 bytes overhead and alignment
/**********************************************************
* Return predecessor, current, successor addresses of a free block.
* bp is the address of the block after the header. 
**********************************************************/
static inline void* PRED_PTR(void * bp){
    return ((char *)(bp));
}
static inline void* SUCC_PTR(void *bp){
    return ((char *)(bp)+WSIZE);
}
static inline void* CURR_PTR(void *bp){
    return ((char *)(bp) + DSIZE);
}
/**********************************************************
* Return addresses stored in predecessor, successor
* metadata of a free block (ie. what is the actual block
* address of a predecessor or successor block?)
* Return the current block (not sure if this is useful),
* but kept it here in case. 
**********************************************************/
static inline void* PRED(void *bp){
    return (*((char **)(bp)));
}
static inline void* SUCC(void *bp){
    return (*((char **)SUCC_PTR(bp)));
}
static inline void* CURR(void *bp){
    return (*((char **)CURR_PTR(bp)));
}
/*************************************************************************
 * Global Variables
*************************************************************************/
void* heap_listp = NULL;
void* prologue_h = NULL; //prologue header
void* epilogue_h = NULL; //epilogue header
int request_id; //this is for debugging comment it out later
static void *segregated_list[MAX_SIZE_CLASS];
static unsigned int flag_coalesce; 
/*************************************************************************
 * Forward Declarations of Helper Functions
*************************************************************************/
//segregated list helpers
static inline size_t map_size_class (size_t size);
void *extend_heap(size_t words);
void insert_free_block (void *free_block);
void remove_free_block (void *bp);
void *coalesce(void *bp);
void * find_fit(size_t asize);
void place(void* bp, size_t asize);
//heap checker helpers
static void myprintblock(void *bp);
static void mycheckblock(void *bp);
static int check_overlap_helper(void *bp);
static int check_hf_consistency(void *bp);
static int check_aligment(void *bp);
static int check_no_uncoalesced_free_blocks(void *bp);
static int check_valid_address_helper(void *bp);
static void myheapcheck(void);
static void mm_printblock(void *bp);
static int coalesce_block_bookkeeping(void);
static int checkheapvalid(void);
static int check_free_list_consistency(void);
static void mm_print_seglist(void);
static void mm_print_freelist(unsigned int list_index);
static void mm_printheap(void);
int mm_check(void);
static void mm_check_wrapper(void);
/**********************************************************
* Function that maps a given size to a size class.  
* Corner case: if we get too big a size, need to handle this
* while adding/removing a free block. 
**********************************************************/
static inline size_t map_size_class (size_t size){
    size_t bsize = size/MINIMUM_BLOCK_SIZE;
    size_t size_class = 0;
    while ((bsize >>= 1) != 0){
        size_class++;
    }
    return size_class;
} 
/**********************************************************
*  insert a free block to the explicit list.
*  size is in bytes. we map it to an appropriate class below.
*  debug this function very carefully
**********************************************************/
void insert_free_block (void *free_block){
    if (free_block == NULL){return;}
    //find appropriate size class
    size_t size_class = map_size_class(GET_SIZE(HDRP(free_block)));
    size_class = (size_class >= MAX_SIZE_CLASS) ? (MAX_SIZE_CLASS - 1) : size_class;
    /*LIFO Policy: Insert @ tail
     *Address-ordered policy: go through the linked list and
     *check the address of the block to be inserted with the
     *address of the current block and addresss of the successor block
     *If we reach the head of the list upon traversal, then insert our
     *new block as the new head of the list. 
     */
    void *current;
    current = segregated_list[size_class]; //this might be an offender, debug here if crashes
    //if we found a suitable position in the list
    if (current != NULL){
            PUT(PRED_PTR(free_block), current);
            PUT(SUCC_PTR(current), free_block);
            PUT(SUCC_PTR(free_block), NULL);
            segregated_list[size_class] = free_block;
    }
    //this block does not belong on this free list
    else {
        PUT(PRED_PTR(free_block), NULL);
        PUT(SUCC_PTR(free_block), NULL);
        segregated_list[size_class] = free_block; //could be an offender
    }
}
/**********************************************************
*  remove a free block from the explicit list.
*  size is in bytes. we map it to an appropriate class below.
**********************************************************/
void remove_free_block (void *bp){
    //WHAT IF BP IS NULL??
    size_t size_class = map_size_class(GET_SIZE(HDRP(bp)));
    size_class = (size_class >= MAX_SIZE_CLASS) ? (MAX_SIZE_CLASS - 1) : size_class;
    /* when we remove from a list: 
     * predecessor's successor points to successor block,
     * and vice versa.
     * For the sake of clarity, assume we have the current block, the pred block
     * and the succ block. 
     * Pred block has ptrs PRED, SUCC storing values *PRED, *SUCC respectively.
     * Succ block has ptrs PRED1, SUCC1 storing values *PRED1, *SUCC1 respectively.
     * We want: *SUCC = PRED1; *PRED1 = SUCC; 
     */
    if (PRED(bp) != NULL){
        if (SUCC(bp) != NULL){
            PUT(SUCC_PTR(PRED(bp)), SUCC(bp));
            PUT(PRED_PTR(SUCC(bp)), PRED(bp));
        }
        else {
            //curr block was last element of the list
            PUT(SUCC_PTR(PRED(bp)), NULL);
            segregated_list[size_class] = PRED(bp); //class points to new tail
        }
    }
    else {
        //curr block was first element of the list
        if (SUCC(bp) != NULL){
            PUT(PRED_PTR(SUCC(bp)), NULL);
        }
        else {
            //that was the only element on list
            segregated_list[size_class] = NULL;
        }
    }
}
/**********************************************************
 * mm_init
 * Initialize the heap, including "allocation" of the
 * prologue and epilogue
 **********************************************************/
/***********************SMARTER IMPLICIT LIST VERSION WITH NEANDER_MM_CHECK**********************/
// int mm_init(void)
// {
//     request_id = -1; 
//     char *bp;

//     //check consistency

//    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
//          return -1;
//      PUT(heap_listp, 0);                         // alignment padding
//      PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));   // prologue header
//      PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));   // prologue footer
//      PUT(heap_listp + (3 * WSIZE), PACK(0, 1));    // epilogue header
//      heap_listp += DSIZE;

//      // check consistency
//      printf("before extend:\n");
//      myheapcheck();

//     /* Extend the empty heap with a free block of CHUNKSIZE bytes */
//      if ((bp = extend_heap(4*CHUNKSIZE)) == NULL)
//         return -1;

//      printf("after extend:\n");
//      myheapcheck();

//      // exit(0); //for debugging purposes
//      return 0;
//  }
/***********************SEGREGATED LIST VERSION**********************/
int mm_init(void)
{
    //request_id = -1; 
    flag_coalesce = 1; 
    heap_listp = NULL;
    prologue_h = NULL; epilogue_h = NULL;

    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
         return -1;
     PUT(heap_listp, 0);                         // alignment padding
     PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));   // prologue header
     PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));   // prologue footer
     PUT(heap_listp + (3 * WSIZE), PACK(0, 1));    // epilogue header

    //prologue_h = heap_listp + (1 * WSIZE);
    //printf("PH: %zu\n", GET_ALLOC(prologue_h));
    epilogue_h = heap_listp + (3 * WSIZE);
    //printf("EH: %zu\n", GET_ALLOC(epilogue_h));
    heap_listp += DSIZE;
     //myprintblock(prologue_h);
     //myprintblock(epilogue_h);
     // // check consistency
     // printf("before extend:\n");
     // myheapcheck();
    //initialize segregated free list to point to NULL for each free list.
    for (int i = 0; i < MAX_SIZE_CLASS; i++){
        segregated_list[i] = NULL;
    }     

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
     if ((extend_heap(CHUNKSIZE/WSIZE)) == NULL)
        return -1;

     // printf("after extend:\n");
     // myheapcheck();

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
/************************WORKING IMPLICIT VERSION**********************************/
// void *coalesce(void *bp)
// {
//     size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
//     size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
//     size_t size = GET_SIZE(HDRP(bp));

//     if (prev_alloc && next_alloc) {       /* Case 1 */
//         return bp;
//     }

//     else if (prev_alloc && !next_alloc) { /* Case 2 */
        
//         remove_free_block();

//         size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
//         PUT(HDRP(bp), PACK(size, 0));
//         PUT(FTRP(bp), PACK(size, 0));
//         return (bp);
//     }

//     else if (!prev_alloc && next_alloc) { /* Case 3 */
//         size += GET_SIZE(HDRP(PREV_BLKP(bp)));
//         PUT(FTRP(bp), PACK(size, 0));
//         PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
//         return (PREV_BLKP(bp));
//     }

//     else {            /* Case 4 */
//         size += GET_SIZE(HDRP(PREV_BLKP(bp)))  +
//             GET_SIZE(FTRP(NEXT_BLKP(bp)))  ;
//         PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
//         PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
//         return (PREV_BLKP(bp));
//     }
// }
/************************SEG:LIFO**********************************/
void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    void *coalesced_ptr = NULL; 
    if (prev_alloc && next_alloc) {       /* Case 1 */
        //coalesced_ptr = bp;
        return bp;
    }
    else if (prev_alloc && !next_alloc) { /* Case 2 */
        //remove next block from free list, coalesce, then mark the coalesced block
        remove_free_block(bp);
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        coalesced_ptr = bp;
    }
    else if (!prev_alloc && next_alloc) { /* Case 3 */
        remove_free_block(bp);
        remove_free_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        coalesced_ptr = PREV_BLKP(bp);
    }

    else {            /* Case 4 */
        remove_free_block(bp);
        remove_free_block(PREV_BLKP(bp));
        remove_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))  +
            GET_SIZE(FTRP(NEXT_BLKP(bp)))  ;
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        coalesced_ptr = PREV_BLKP(bp);
    }

    insert_free_block(coalesced_ptr); //add the new 
    // mm_printheap();
    // mm_print_seglist();
    return coalesced_ptr;
}
/**********************************************************
 * extend_heap
 * Extend the heap by a given number of words, maintaining alignment
 * requirements of course. Free the former epilogue block
 * and reallocate its new header
 **********************************************************/
void *extend_heap(size_t words)
{
    char *bp; 
    size_t size;
    // mm_print_seglist();
    //HEAPCHECK HERE TO MAKE SURE EVERYTHING IS CONSISTENT
    /* Allocate an even number of words to maintain alignments */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    
    // If the last block is free, extend the heap by remainder needed.
    //Actually this might not be such a great thing. Naive extension might be better. 
    if (GET_ALLOC(epilogue_h - WSIZE) == 0){
        size_t available_free_space = GET_SIZE(epilogue_h - WSIZE); 
        size -= available_free_space;
    }

    if ( (bp = mem_sbrk(size)) == (void *)-1 )
        return NULL;
    // mm_printheap();
    // mm_print_seglist();

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));                // free block header
    PUT(FTRP(bp), PACK(size, 0));                // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));        // new epilogue header
    epilogue_h = HDRP(NEXT_BLKP(bp)); //keep track of new epilogue for checks
    //Insert new free chunk into the segregated list.
    insert_free_block(bp);
    // mm_printheap();
    // mm_print_seglist();
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
/**********************************************************
 * find_fit
 * Traverse the heap searching for a block to fit asize
 * Return NULL if no free blocks can handle that size
 * Assumed that asize is aligned
 **********************************************************/
 /****************REFERENCE***************************/
// void * find_fit(size_t asize)
// {
//     void *bp;
//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
//     {
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
//         {
//             return bp;
//         }
//     }
//     return NULL;
// }
/**********************************************************
 * place
 * Mark the block as allocated
 **********************************************************/
void place(void* bp, size_t asize)
{
  /* Get the current block size */
    if (bp == NULL) {return;}
  size_t bsize = GET_SIZE(HDRP(bp));
  assert(bsize >= asize); //should be allocating to a suitably big free block 
  size_t split_size = bsize - asize;
  
  // mm_print_seglist();
  remove_free_block(bp);
  // mm_print_seglist();

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
    //for segregated list, insert the remainder free block into the correct list. 
    insert_free_block(NEXT_BLKP(bp)); //make sure the size of this block is correct
  }
  // for debugging purposes
  // if (request_id == 3)
  //   exit(0);
  // request_id++;
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
    // mm_printheap();
    // mm_print_seglist();
    // mm_check_wrapper();
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    //NORMAL HEAP CHECKs here
    insert_free_block(bp);
    if (flag_coalesce){
    coalesce(bp);
    }     
    // printf("After free(%p):\n",bp);
    // mm_check_wrapper(); // myheapcheck();
}
/**********************************************************
 * mm_malloc
 * Allocate a block of size bytes.
 * The type of search is determined by find_fit
 * The decision of splitting the block, or not is determined
 *   in place(..)
 * If no block satisfies the request, the heap is extended
 ***************************REFERENCE CODE*******************************/
    // if ((bp = find_fit(asize)) != NULL) {
    //     place(bp, asize);
    //     //printf("After malloc(%zu): malloc(%zu)\n", size, asize);
    //     //myheapcheck();
    //     return bp;
    // }
    /* No fit found. Get more memory and place the block */
/*******************************************************************/
void *mm_malloc(size_t size)
{
    size_t asize; /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char * bp;
    // printf("Before malloc(%zu):\n",size);
    // mm_check_wrapper(); // myheapcheck();
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/ DSIZE);
    /* Search the free list for a fit */
    size_t size_class; 
    size_class = MIN(map_size_class(asize), MAX_SIZE_CLASS-1);
    // can size class fail/return an erroneous value? check
    int index;
    for (index = size_class; index < MAX_SIZE_CLASS; index++){
        bp = segregated_list[index];
        if (bp != NULL){
            while (bp != NULL && (asize > GET_SIZE(HDRP(bp)))){
                bp = PRED(bp);
            }
            if (bp == NULL){continue;}
            //found a suitable fit.
            // mm_printheap();
            //mm_print_freelist(index);
            place(bp, asize);
            // mm_check_wrapper();
            return bp;
        }
    }

    extendsize = MAX(asize, PAGE_SIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    // mm_printheap();
    place(bp, asize);
    // printf("After malloc(%zu): malloc(%zu)\n", size, asize);
    // myheapcheck();
    // mm_check_wrapper();
    return bp;
}
/**********************************************************
 * mm_realloc
 * If ptr = NULL, return mm_malloc(size)
 * If size = 0, mm_free(ptr) then return NULL
 * If the oldsize is sufficient, just return the ptr
 * For reallocation: 
 * Rather than malloc first and then free the old block,
 * I first free the old block to take advantage of any
 * physically adjacent free blocks. To make sure that data (payload)
 * isn't lost, we first store copies of the first 2 words of the
 * oldptr block (this will be replaced by pred_ptr and succ_ptr once
 * freed) and also prevent the block from coalescing during the free
 * (do make sure we still have access to that block). Then, re-enable
 * coalescing and mm_malloc(size) where the allocation is done along with
 * necessary coalescing and splitting. After that, we copy over the contents
 * of the old block to the new one, and also paste back the first 2 words that
 * got replaced by free metadata.  

/*********************************************************/
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
    size_t oldSize, asize;
    oldSize = GET_SIZE(HDRP(oldptr));
    asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/ DSIZE);
    //if our original size is good enough, no need to do any allocation, 
    //our current pointer is good enough.
    if (asize <= oldSize){
        assert(ptr != NULL); //should have handled this already
        return ptr; 
    }

    //copy the 1st 2 words of the current payload to save these from getting
    //replaced by the PRED & SUCC once freed.
    uintptr_t payload_word1 = GET(oldptr);
    uintptr_t payload_word2 = GET(oldptr+WSIZE);    
    //temporarily disable coalescing to keep track of the old payload data
    flag_coalesce = 0;
    mm_free(oldptr);
    flag_coalesce = 1; 

    void *newptr;
    newptr = mm_malloc(size*2);
    if (newptr == NULL){
        return NULL;
    }

    /* Copy the old data. */
    size_t copySize = oldSize;
    if (size < copySize)
      copySize = size;    
    memcpy(newptr, oldptr, copySize);
    //rewrite the (saved) first two words of the payload that got lost while
    //freeing
    PUT(newptr, payload_word1);
    PUT(newptr+WSIZE, payload_word2);
    return newptr;
}
/**********************DEBUG*************************************/
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
/**********************************************************
 * Prints out a given block with overhead and payload info
 * Neanderthal version.  
 *********************************************************/
// static void myprintblock(void *bp){
//     volatile size_t hdr_alloc = GET_ALLOC(HDRP(bp));
//     volatile size_t hdr_size = GET_SIZE(HDRP(bp));
//     volatile char alloc_h = hdr_alloc ? 'a' : 'f';

//     volatile size_t ftr_alloc = GET_ALLOC(FTRP(bp));
//     volatile size_t ftr_size = GET_SIZE(FTRP(bp));
//     volatile char alloc_f = ftr_alloc ? 'a' : 'f';

//     size_t payload_size = hdr_alloc ? hdr_size - DSIZE : 0;
//     if (alloc_h == 'a'){
//         printf("a: header: [%zu,%c,%d,%zu] footer: [%zu,%c]\n", hdr_size, alloc_h, request_id, payload_size, ftr_size, alloc_f);
//     }
//     if (alloc_h == 'f'){
//         printf("f: header: [%zu,%c] footer: [%zu,%c]\n", hdr_size, alloc_h, ftr_size, alloc_f);
//     }
// }

// /**********************************************************
//  * Checks that free blocks have been coalesced. 
//  * Corner cases: start and end of heap
//  *********************************************************/
// static int check_no_uncoalesced_free_blocks(void *bp){
//     int result = 1;
//     size_t bp_alloc = GET_ALLOC(HDRP(bp));
//     size_t next_bp_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));    
//     size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
//     size_t prev_bp_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
//     size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
//     unsigned int prev_blk_free = (prev_bp_size != 0) && (prev_alloc == 0);
//     unsigned int next_blk_free = (next_bp_size != 0) && (next_alloc == 0);

//     //corner cases
//     if (bp_alloc == 0){
//         if (prev_blk_free || next_blk_free){
//             fprintf(stderr, "mm_check: uncoalesced free blocks!\n");
//             result = 0;
//             assert (0); //this error will need enough debugging to warrant crashing it here
//         }
//     }
//     return result; 
// } 
// /**********************************************************
//  * Checks header-footer consistency & alignment.
//  * Return non-zero if pass.
//  *********************************************************/
// static int check_hf_consistency(void *bp){
//     int result = 1;
//     volatile size_t hdr_size = GET_SIZE(HDRP(bp));
//     volatile size_t hdr_alloc = GET_ALLOC(HDRP(bp));
//     volatile size_t ftr_size = GET_SIZE(FTRP(bp));
//     volatile size_t ftr_alloc = GET_ALLOC(FTRP(bp));
//     //check header consistency
//     if (hdr_size != ftr_size || hdr_alloc != ftr_alloc){
//         fprintf(stderr, "mm_check: header-footer consistency failed!\n");
//         result = 0;
//         assert(0); //failed header-footer consistency check
//     }    
//     return result;
// }

// static int check_aligment(void *bp){
//     int result = 1;
//     assert(check_hf_consistency(bp) != 0); //no metadata incosistency
//     if (!((size_t)HDRP(bp) % DSIZE) || !((size_t)HDRP(NEXT_BLKP(bp)) % DSIZE)) {
//         fprintf(stderr, "mm_check: alignment test failed!\n");
//         result = 0;
//         assert(0);
//     }
//     return result; 
// }
// /**********************************************************
//  * For a given block ptr, Checks if we have overlapped 
//  * into an adjacent block.
//  *********************************************************/
// static int check_overlap_helper(void *bp){
//     int result = 1;
//     if ((uintptr_t)FTRP(bp) > (uintptr_t)HDRP(NEXT_BLKP(bp))){
//         fprintf(stderr, "mm_check: overlap check failed!\n");
//         result = 0;
//         assert(0);
//     }
//     return result;
// }
// /**********************************************************
//  * Check is an address is a valid heap address.
//  *********************************************************/
// static int check_valid_address_helper(void *bp){
//     int result = 1;
//     if (bp < heap_listp || bp >= epilogue_h){
//         fprintf(stderr, "mm_check: not a valid heap address!\n");
//         result = 0;
//         //assert(0);
//     }
//     return result;
// }

// /**********************************************************
//  * Neanderthal mm_check.
//  *********************************************************/
// static void mycheckblock(void *bp){
//     volatile size_t hdr_size = GET_SIZE(HDRP(bp));
//     volatile size_t hdr_alloc = GET_ALLOC(HDRP(bp));
//     volatile size_t ftr_size = GET_SIZE(FTRP(bp));
//     volatile size_t ftr_alloc = GET_ALLOC(FTRP(bp));
//     //check header consistency
//     if (hdr_size != ftr_size || hdr_alloc != ftr_alloc){
//         fprintf(stderr, "my_check: header-footer consistency failed!\n");
//         assert(0); //failed header-footer consistency check
//     }
//     //check if aligned
//     if (!((size_t)HDRP(bp) % DSIZE) || !((size_t)HDRP(NEXT_BLKP(bp)) % DSIZE)) {
//         fprintf(stderr, "my_check: alignment test failed!\n");
//         assert(0);
//     }
//     return;
// }

// static void myheapcheck(void){
//     char *bp;
//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
//         myprintblock(bp);
//         // mycheckblock(bp);
//         // check_hf_consistency(bp);
//         // check_aligment(bp);
//         // check_no_uncoalesced_free_blocks(bp);
//         // check_overlap_helper(bp);
//     }
//     printf("my_check: pass\n");    
// }
// /**********************************************************
//  * Segregated list mm_check helpers:
//  *********************************************************/
// /**********************************************************
//  * Prints out a given block with overhead and payload info
//  * Segregated list version.  
//  *********************************************************/
// static void mm_printblock(void *bp){
//     volatile size_t hdr_alloc = GET_ALLOC(HDRP(bp));
//     volatile size_t hdr_size = GET_SIZE(HDRP(bp));
//     volatile char alloc_h = hdr_alloc ? 'a' : 'f';

//     volatile size_t ftr_alloc = GET_ALLOC(FTRP(bp));
//     volatile size_t ftr_size = GET_SIZE(FTRP(bp));
//     volatile char alloc_f = ftr_alloc ? 'a' : 'f'; 

//     size_t payload_size = hdr_alloc ? hdr_size - DSIZE : 0;
//     if (alloc_h == 'a'){
//         printf("a: header: [%zu,%c,%zu] footer: [%zu,%c]\n", hdr_size, alloc_h, payload_size, ftr_size, alloc_f);
//     }
//     if (alloc_h == 'f'){
//         printf("f: header: [%zu,%c] pred: [%p] next:[%p] footer: [%zu,%c]\n", hdr_size, alloc_h, PRED(bp), SUCC(bp), ftr_size, alloc_f);
//     }
// }
// /**********************************************************
//  * Prints out all blocks in a free list.
//  * This function actually causes a SIGSEGV while testing!
//  * Fix if really necessary, so far it's been useful as a rubber duck.
//  *********************************************************/
// static void mm_print_freelist(unsigned int list_index){
//     char *block;
//     block = segregated_list[list_index];
//     if (block == NULL){printf("Empty class\n"); return;}
//     for (; GET_SIZE(HDRP(block)) > 0; block = PRED(block)){
//         mm_printblock(block);
//     }
// }
// /**********************************************************
//  * Prints out all free lists. Shows a logical linked list
//  * diagram for each free list in the segregated list. 
//  * Remember, linked lists are in reverse order (the last block
//  * in the list is actually the first free block inserted).
//  *********************************************************/
// static void mm_print_seglist(void){
//     for (int i = 0; i < MAX_SIZE_CLASS; i++){
//         printf("\t[Class#%d]:", i);
//         void *current_block = segregated_list[i]; //start at tail of list
//         printf("NULL <-> ");  
//         while (current_block != NULL){
//             printf("%p(s:%zu a:%zu) <-> ", current_block, GET_SIZE(HDRP(current_block)), GET_ALLOC(HDRP(current_block)));
//             current_block = PRED(current_block);
//         }
//         printf("NULL\n");
//     }
// }
// /**********************************************************
//  * Prints out the heap. 
//  *********************************************************/
// static void mm_printheap(void){
//     char *bp;
//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
//         printf("%p:(%zu,%zu) --> ", bp, GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)));
//     }
//     printf("END\n");    
// }
// /**********************************************************
//  * Traverse through all free lists and check if each block
//  * is in the correct size class, is marked as free.
//  * check predecessor/successor consistency. 
//  *********************************************************/
// static int check_free_list_consistency(void){
//     for (int i = 0; i < MAX_SIZE_CLASS; i++){
//         void *bp = segregated_list[i];
//         void *succ = NULL;
//         printf("mm_check: Free list #%d consistency: ", i);
//         while (bp != NULL){
//             if (GET_ALLOC(HDRP(bp))){
//                 fprintf(stderr, "FAILED: %p is not a free block!\n", bp);
//                 return 0;
//             }
//             if (GET_SIZE(HDRP(bp)) < (1<< i)*MINIMUM_BLOCK_SIZE || 
//                 (i != MAX_SIZE_CLASS-1 && GET_SIZE(HDRP(bp)) >= (1<<(i+1))*MINIMUM_BLOCK_SIZE)) {
//                 fprintf(stderr, "\n FAILED: Block %p is in the wrong free list. Size = %zu\n", bp, GET_SIZE(HDRP(bp)));
//                 return 0;
//             }
//             if (succ != SUCC(bp)){
//                 fprintf(stderr, "\nFAILED: incosistent pred/succ info, check block %p!\n", bp);
//                 fprintf(stderr, "Current successor pointer is %p, successor address value stored in block is %p\n",succ,SUCC(bp));
//                 //asssert(0);
//                 return 0;
//             }
//             if (SUCC(bp) != NULL && GET_ALLOC(HDRP(SUCC(bp)))){
//                 fprintf(stderr, "\nFAILED: not pointing to a free block!\n");
//                 return 0;
//             }
//             succ = bp;
//             bp = PRED(bp);
//         }
//         printf("PASS\n");
//     }
//     printf("mm_check: Free list consistency check: PASS!\n");
//     return 1;
// }
// /**********************************************************
//  * Traverse through all free lists and check if the block physically
//  * adjacent is free. If so, we forgot to coalesce!
//  * Also traverse through the entire heap and count if we missed 
//  * adding any free blocks to the segregated list!
//  *********************************************************/
// static int coalesce_block_bookkeeping(void){
//     unsigned int free_blocks_seglist = 0;
//     unsigned int free_blocks_heap = 0;
//     printf("mm_check: coalescing and matching errors:\n");
//     for (int i = 0; i < MAX_SIZE_CLASS; i++){
//         void *bp = segregated_list[i];
//         while (bp != NULL){
//             if (GET_ALLOC(HDRP(bp))){
//                 fprintf(stderr, "mm_check: Allocated block %p in free list#%d! FAIL!\n",bp,i);
//                 assert(0);  //crash here; we're not checking for frees specifically 
//                             //and if something's wrong here it's time to debug before moving on
//             }
//             free_blocks_seglist++;
//             //check for coalescing errors
//             check_no_uncoalesced_free_blocks(bp);
//             bp = PRED(bp);
//         }
//     }

//     //Now check the entire heap to see if we missed any free blocks
//     char *block;
//     for (block = heap_listp; GET_SIZE(HDRP(block)) > 0; block = NEXT_BLKP(block)){
//         if (!GET_ALLOC(HDRP(block))){
//             free_blocks_heap++;
//         }
//     }
//     if (free_blocks_heap != free_blocks_seglist){
//         fprintf(stderr, "mm_check: Missed free blocks in the heap!\n");
//         return 0;
//     }
//     printf("PASS!\n");
//     return 1;
// }
// /**********************************************************
//  * mm_check version of myheapcheck which checks for basic errors
//  * in the heap
//  *********************************************************/
// static int checkheapvalid(void){
//     char *bp;
//     printf("HEAP VALIDITY CHECK: ");
//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
//         if (check_hf_consistency(bp) == 0){
//             fprintf(stderr, "\nFAILED: hf consistency failed for block %p!\n", bp);
//             //assert(0);
//             return 0;
//         }
//         if (check_aligment(bp) == 0){
//             fprintf(stderr, "\nFAILED: hf alignment failed for block %p!\n", bp);
//             //assert(0);
//             return 0;                
//         }
//         if (check_no_uncoalesced_free_blocks(bp) == 0){
//             fprintf(stderr, "\nFAILED: missed coalescing around block %p!\n", bp);
//             //assert(0);
//             return 0;
//         }
//         if (check_overlap_helper(bp) == 0){
//             fprintf(stderr, "\nFAILED: block %p is overlapping over block %p!\n", bp, NEXT_BLKP(bp));
//             //assert(0);
//             return 0;            
//         }
//         if (check_valid_address_helper(bp) == 0){
//             fprintf(stderr, "Not a valid heap address: %p!\n", bp);
//             return 0;
//         }
//     }
//     printf("PASS!\n");
//     return 1;
// }
// /**********************************************************
//  * The beast.
//  *********************************************************/
// int mm_check(void){

//     mm_printheap();
//     mm_print_seglist();
//     // for (int i = 0; i < MAX_SIZE_CLASS; i++){
//     //     mm_print_freelist(i);
//     // }
//   return (checkheapvalid() && check_free_list_consistency() && coalesce_block_bookkeeping());
// }

// static void mm_check_wrapper(void){
//     if (mm_check()==0){
//         printf("mm_check: HEAP CHECK FAILED!\n");
//         assert(0);
//     }
// }
