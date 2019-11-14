/* This allocator implements a segregated free list to
 * manage all the free blocks based on size classes. 
 * Each index in the hash table represents the size of
 * the block as a power of 2 with a max size of HASH_SIZE.
 * 
 * Allocated blocks contain an 8 byte header and footer a
 * minimum of 16 bytes for the payload. The lowest
 * bit of the header indicates whether the block 
 * is allocated (1) or free (0). In this case, 
 * the bit is set to 1. The most significant 58 bits
 * are used for the size since each block is 
 * a multiple of 8.
 *
 * Freed blocks contain an 8 byte header and 8 byte 
 * footer which contain the size and the allocated bit
 * as the lowest bit. In this case it will be set to 0.
 * In addition, freed blocks will store the pointer to the
 * next block's header within the word following its own
 * header. A pointer to the previous block's header is stored
 * in the next word after.
 *
 * When a block is freed, the allocator bit is set to 0 and
 * goes through coalesce process. The block is then 
 * added to the segregated free list. The block is hashed 
 * using its block size and added to the front of
 * the linked list of blocks.
 *
 * When malloc and realloc are called, the hash table is accessed
 * based on the size argument passed in (minimum being 32 bytes).
 * From there the first block is taken from the linked list.
 *
 * Blocks are coalesced when a block is free'd or when
 * an edge case is encountered where the last block of the
 * heap is free and the heap needs to be extended. In this 
 * case, the new block will be composed of the existing free
 * block and a new heap extension with size being the difference
 * between the size argument and the free block available.
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 *
 * Function Declarations
 *
 ********************************************************/
void * coalesce(void *bp);                      //coalesces the block pointed at by bp. Checks all four cases.
void * extend_heap(size_t size);                //Extends the heap utilizing the free blocks in the segregated list. Keeps current contents.
void * get_fit(size_t asize);                   //Defines the policy for finding a free block that fits the size argument.
void   place(void* bp, size_t asize);           //Marks the header and footer of the block as allocated with the size argument. 

static inline size_t    map_size_class(size_t size);                 //Hashes the key and converts it to an index for the segregated free list hash table
void   insert_free_block(void * free_block);       //Adds the free block to the segregated list
void   remove_free_block(void * free_block);  //Removes a free block from the segregated list
bool   is_block_in_seglist(void * block);       //Quick check to see if a block is in the segregated list.
bool   is_block_in_freelist(void * block);      //Quick check to see if a block is in the free list.

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
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/*************************************************************************
 * Basic Constants and Macros
 * You are not required to use these macros but may find them helpful.
*************************************************************************/
#define WSIZE       sizeof(void *)            /* word size (bytes) */
#define DSIZE       (2 * WSIZE)            /* doubleword size (bytes) */

#define MAX(x,y) ((x) > (y)?(x) :(y))
#define MIN(x,y) ((x) <= (y)?(x) :(y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)          (*(uintptr_t *)(p))
#define PUT(p,val)      (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)    (GET(p) & 0x1)

/* Get the next and prev pointer to free block given pointer to header of a free block */
#define GET_PRED_PTR(p)  (GET((char*)(p)+WSIZE))
#define GET_SUCC_PTR(p)  (GET((char*)(p)+DSIZE))

/* Set the next and prev pointer to free block given pointer to header of a free block */
#define SET_PRED_PTR(p,val)  (PUT((char*)(p)+WSIZE, val))
#define SET_SUCC_PTR(p,val)  (PUT((char*)(p)+DSIZE, val))

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define HASH_SIZE 20

void* prologue_ptr = NULL; //pointer to the prologue block
void* epilogue_ptr = NULL; //pointer to the epilogue block
static void * segList[HASH_SIZE];
bool dont_coalesce = false;

/**********************************************************
 * Hashing function that just calculates the log of 'key'
 *
 * @param key = integer who's hash needs to be computed
 *
 * @return value of the hash index
 *
 **********************************************************/
static inline size_t map_size_class(size_t size)
{
    size_t size_class=0;
    int val = 1;
    for (size_class = 0 ; size_class < HASH_SIZE ; size_class++)
    {
        if (size <= val)
        {
            break;
        }
        val<<=1;
    }
    return MIN(size_class, HASH_SIZE-1);
}

/**********************************************************
 * is_block_in_seglist
 * Checks to see if a block exists in the segregated free list.
 *
 * @param block - the block pointer in question
 *
 * @return bool - true if the block is in the list. 
 *                False otherwise.
 *
 **********************************************************/
bool is_block_in_seglist(void * block)
{
    size_t index = 0;
    
    //Traverse entire segregated list
    while (index < HASH_SIZE)
    {
        void * list_root = segList[index];
        while (list_root!=NULL)
        {
            if (block == list_root) //Looks like the block pointer exists in the list
            {
                return true;
            }
            list_root = (void *)GET_PRED_PTR(list_root);
        }
        index ++;
    }

    return false;
}

/**********************************************************
 * add_to_seglist
 * Adds a block that has been set as free to the segregated 
 * free list.
 *
 * @param free_block - a pointer to the free block being
 *                     added.
 *
 * @return void
 *
 **********************************************************/
void insert_free_block(void * free_block)
{
    // Make sure the block does not already exist in the segregated free list
    //  assert(!is_block_in_seglist(free_block));

    size_t index = map_size_class(GET_SIZE(free_block));
    void* old_first_block = segList[index];
    segList[index] = free_block;

    SET_PRED_PTR(free_block, (uintptr_t)old_first_block);
    SET_SUCC_PTR(free_block, (uintptr_t)NULL);

    if (old_first_block)
    {
        SET_SUCC_PTR(old_first_block, (uintptr_t)free_block);
    }

    return;
}

/**********************************************************
 * is_block_in_freelist
 * Checks to see if a block exists in its respective bin in the segregated free list.
 *
 * @param block - the block pointer in question
 *
 * @return bool - true if the block is in the list. 
 *                false otherwise.
 *
 **********************************************************/
bool is_block_in_freelist(void * block)
{
    size_t index = map_size_class(GET_SIZE(block));
    void * list_root = segList[index];

    while (list_root!=NULL)
    {
        if (block == list_root)
        {
            return true;
        }
        list_root = (void *)GET_PRED_PTR(list_root);
    }

    return false;
}

/**********************************************************
 * remove_from_seglist
 * Removes a free block from the segregated list
 *
 * @param free_block - a pointer to the free block being
 *                     being removed.
 *
 * @return void
 *
 **********************************************************/
void remove_free_block(void * free_block)
{
    // Make sure the block is in the proper bin in the segregated free list
    // assert(is_block_in_freelist(free_block));

    uintptr_t next = GET_PRED_PTR(free_block); // next pointer
    uintptr_t prev = GET_SUCC_PTR(free_block); // prev pointer

    if (next)
    {
        SET_SUCC_PTR(next, prev); // next's prev = prev
    }

    if (prev)
    {
        SET_PRED_PTR(prev, next); // prev's next = next
    }
    else
    {
        int index = map_size_class(GET_SIZE(free_block));
        segList[index] = (void *)next;
    }

    return;
}

/**********************************************************
 * mm_init
 * Initialize the heap, including "allocation" of the
 * prologue and epilogue
 **********************************************************/
int mm_init(void)
{
//  mm_check();

    void* heap_listp;
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        {return -1;}
    PUT(heap_listp, 0);                         // alignment padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));   // prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));   // prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));    // epilogue header
    prologue_ptr = heap_listp + (1 * WSIZE);
    epilogue_ptr = heap_listp + (3 * WSIZE);

    heap_listp += DSIZE;

    int itr=0;
    for(; itr<HASH_SIZE; itr++)
    {
        segList[itr] = (void *)NULL;    //initialize each element in the segregated free list to NULL
    }

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
    /******************************************************
     * Steps for coalescing:
     * 1) Check if two blocks beside current block is free
     * 2) If there is a block to the left, update 
     *    its header with new length
     *       a)Otherwise, update current block's header 
     *         with new length
     * 3) If there is a block to the right, update its 
     *    footer with new length
     *       b)Otherwise, update current block's footer 
     *         with new length
     *
     * NOTE: I'm assuming that the current block bp was
     * never in the free list to begin with. May be worth
     * revisiting.
     ******************************************************/

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    //Let's calculate the header pointer of all three blocks
    void *prev_header = HDRP(PREV_BLKP(bp));
    void *next_header = HDRP(NEXT_BLKP(bp));

    //Let's calculate the footer pointer of all three blocks
    void *next_footer = FTRP(NEXT_BLKP(bp));

    
    if (prev_alloc && next_alloc)               /* Case 1 - No coalescing necessary*/
    {
        return bp;
    }

    else if (prev_alloc && !next_alloc)        /* Case 2 - Coalesce current block with the next block */
    {
        // Remove next block from the appropriate free list
        remove_free_block(next_header);

        // Merge the prev and curr blocks
        size += GET_SIZE(next_header);

        PUT(HDRP(bp), PACK(size, 0));
        PUT(next_footer, PACK(size, 0));
        
        return (bp);
    }

    else if (!prev_alloc && next_alloc)        /* Case 3 - Coalesce current block with the previous  */
    {
        // Remove next block from the appropriate free list
        remove_free_block(prev_header);
        
        // Merge the next and curr blocks
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

        return (PREV_BLKP(bp));
    }

    else            /* Case 4 - Coalesce current block with both the previous and next block*/
    {
        // Remove the prev and next block from the appropriate free lists
        remove_free_block(prev_header);
        remove_free_block(next_header);

        // Merge the prev, curr, and next blocks
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))  +
            GET_SIZE(next_footer)  ;
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(next_footer, PACK(size,0));

        return (PREV_BLKP(bp));
    }
}

/**********************************************************
 * extend_heap
 * Extend the heap by "words" words, maintaining alignment
 * requirements of course. Free the former epilogue block
 * and reallocate its new header
 **********************************************************/
void *extend_heap(size_t size)
{
    char *bp;

    // If the previous block is free, only extend the heap by (size - size_of_prev_free_block) so that you reduce external fragmentation
    size_t size_prev_free = GET_SIZE(epilogue_ptr-WSIZE) * !GET_ALLOC(epilogue_ptr-WSIZE);
    size -= size_prev_free;

    assert (size % DSIZE == 0);

    if ( (bp = mem_sbrk(size)) == (void *)-1 )
    {
        return NULL;
    }

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));                // free block header
    PUT(FTRP(bp), PACK(size, 0));                // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));        // new epilogue header

    epilogue_ptr = HDRP(NEXT_BLKP(bp));

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/**********************************************************
 * break_block_and_return_bp
 * Breaks the block into two segments: one block consisting 
 * of asize bytes and another with a size
 * of original block size minus asize
 *
 * @param block - A pointer to the block
 * @param asize - The size needed from the block
 *
 * @return void * the pointer to the block with size asize
 *
 **********************************************************/
void * break_block_and_return_bp(void * block, size_t asize)
{
    size_t block_size = GET_SIZE(block);
    remove_free_block(block);

    size_t fragment_size = block_size - asize;

    // If fragment is the minimum size of a free block (4 words), break it up
    if (fragment_size >= WSIZE*4)
    {
        // Create a block of asize
        PUT(block, PACK(asize,0));
        PUT(block+asize-WSIZE, PACK(asize,0));

        // Create a block of fragment_size
        PUT(block+asize, PACK(fragment_size,0));
        PUT(block+block_size-WSIZE, PACK(fragment_size,0));

        // Add the new fragment to the segList
        insert_free_block(block+asize);
    }

    return block+WSIZE;
}

/**********************************************************
 * find_fit
 * Traverse the heap searching for a block to fit asize
 * Return NULL if no free blocks can handle that size
 * Assumed that asize is aligned
 **********************************************************/
void * find_fit(size_t asize)
{
    int index = map_size_class(asize);
    void * list_itr;

    while (index < HASH_SIZE)
    {
        list_itr = segList[index];
        while (list_itr!=NULL)
        {
            //First fit search.
            //Split the free block and allocate the necessary bytes
            //The half that remains free will be added to the correct 
            //size class in the segregated list.
            if (GET_SIZE(list_itr) >= asize)
            {
                return break_block_and_return_bp(list_itr, asize);
            }
            list_itr = (void *)GET_PRED_PTR(list_itr);
        }
        index ++;
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

    PUT(HDRP(bp), PACK(bsize, 1));
    PUT(FTRP(bp), PACK(bsize, 1));
}

/**********************************************************
 * mm_free
 * Free the block and coalesce with neighbouring blocks
 **********************************************************/
void mm_free(void *bp)
{
    if(bp == NULL){
      return;
    }
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    if (!dont_coalesce) { bp = coalesce(bp); }
    insert_free_block(HDRP(bp));
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
    char * bp;

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
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    if ((bp = extend_heap(asize)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;

}

/**********************************************************
 * mm_realloc
 * Implemented simply in terms of mm_malloc and mm_free
 *********************************************************/
void *mm_realloc(void *ptr, size_t size)
{
    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0)
    {
      mm_free(ptr);
      return NULL;
    }
    /* If oldptr is NULL, then this is just malloc. */
    if (ptr == NULL)
    {
      return (mm_malloc(size));
    }

    void *oldptr = ptr;
    void *newptr;
    size_t copySize = GET_SIZE(HDRP(oldptr));
    size_t asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/ DSIZE);

    /* If the size is big enough, return as is */
    if (copySize >= asize)
    {
        return oldptr;
    }

    /* Free before a dynamic allocation via malloc to reduce fragmentation. 
     * If the free block is at the end, it will be reused with the part of 
     * the heap that we will extend. In order to preserve the data in the free block,
     * we need to prevent it from coalescing it with the previous block so that 
     * it is not broken up later at any arbitrary point and the data at those points
     * overwritten by headers and footers.
     *
     *  We also need to save the 2 words where next and previous pointers will be saved
     */
    uintptr_t word1 = GET(oldptr);
    uintptr_t word2 = GET(oldptr+WSIZE);
    
    dont_coalesce = true;
    mm_free(oldptr);
    dont_coalesce = false;

    newptr = mm_malloc(size*2);
    if (newptr == NULL)
    {
        return NULL;
    }

    /* Copy the old data. */
    if (size < copySize)
    {
        copySize = size;
    }
    memcpy(newptr, oldptr, copySize);

    /* Write back the 2 words that were overwritten by next and previous pointers */
    PUT(newptr, word1);
    PUT(newptr+WSIZE, word2);
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
int mm_check(void)
{
    int result = 1;
    size_t itr;

    /* Is every block in the free list marked as free? */
    // Iterate through all indices in the hash table.
    for(itr = 0; itr < HASH_SIZE; itr++)
    {
        void *currNode = segList[itr];
        //Iterate through the list of free blocks within the index
        while(currNode)
        {
            //If a block is allocated in the list, this is an error.
            if(GET_ALLOC(currNode))
            {
                fprintf(stderr, "[mm_check Error] a block in the seglist is still allocated\n");
                result = 0;
            }
            currNode = (void*) GET_PRED_PTR(currNode);
        }   
    }

    /* Are there any contiguous free blocks that somehow escaped coalescing? */
    void *itr_pointer = (char *)prologue_ptr + WSIZE;

    while(itr_pointer != (char *)epilogue_ptr+WSIZE)
    {
        bool currAlloc = GET_ALLOC(HDRP(itr_pointer));
        void * next_bp = NEXT_BLKP(itr_pointer);
        bool nextAlloc = GET_ALLOC(HDRP(next_bp));
        if(!currAlloc && !nextAlloc)
        {
            fprintf(stderr, "[mm_check Error] Two contiguous blocks missed coalescing.\n");
            result = 0;
        }
        /* Does every free block actually exist in the free list */
        if(!currAlloc && !is_block_in_seglist(HDRP(itr_pointer)))
        {
            fprintf(stderr, "[mm_check Error] Free block is not in segregated list \n");
            result = 0;
        }
        itr_pointer = next_bp;
    }

    /* Do the list of blocks in each index of the hash table fit the corresponding size class? */
    // Example: blocks in index 5 are between size 17-32 (2^4<SIZE<=2^5)
    
    //Iterate through hash_table from 0 to HASH_SIZE
    for(itr = 5; itr < HASH_SIZE; itr++)
    {
        int minSize = 1<<(itr-1);
        int maxSize = 1<<(itr);
        void *currNode = segList[itr];
        //Iterate through the list of free blocks within the index
        while(currNode)
        {
            // If a block is outside the size class range, it's an error.
            // If its the last bucket, don't enforce max range since the last bucket
            // stores everything larger than it also
            if(GET_SIZE(currNode) <= minSize || (GET_SIZE(currNode) > maxSize && itr!=HASH_SIZE-1))
            {
                fprintf(stderr, "[mm_check Error] This block is outside its size class range\n");
                result = 0;
            }
            currNode = (void*) GET_PRED_PTR(currNode);
        }   
    }

    return result;

}