/* 
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP2e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"XYZ",
	/* First member's full name */
	"Prachi Agrawal",
	/* First member's email address */
	"201401219@daiict.ac.in",
	/* Second member's full name (leave blank if none) */
	"Devanshi Bansal",
	/* Second member's email address (leave blank if none) */
	"201401115@daiict.ac.in",
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */

#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */

#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

#define MINBLOCK   (4*WSIZE)+8   /*Minimum block size needed*/

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/*To set the 8-bit alignment requirement*/
#define ALIGN(size) (((size_t)(size)+(DSIZE-1)) & ~0x7)

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
/* Structure of allocated block
	 ______ _________ ________
    |Header|  DATA   | FOOTER |
     
*/
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
/*The payload of free block stores the address of next and previous pointers of free blocks*/
/*
    _______ ______ ______ ________ ________
   |HEADER | PREV | NEXT |OLD DATA| FOOTER |
*/
/*methods to get next and previous free blocks pointers*/
#define GET_NEXT_PTR(bp) GET(bp+WSIZE)
#define GET_PREV_PTR(bp) GET(bp)

/*methods to set next and previous free blocks pointers*/
#define SET_NEXT_PTR(bp,qp) (GET_NEXT_PTR(bp)=qp)
#define SET_PREV_PTR(bp,qp) (GET_PREV_PTR(bp)=qp)

/* Global variables: */
static char *heap_listp=0; /* Pointer to first block */  
static char *free_listp=0; /* Pointer to first block of free list*/

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);

//static void *next_fit(size_t asize);
static void *find_fit(size_t asize);

//static void *best_fit(size_t asize);
static void place(void *bp, size_t asize);

/*to maintain free list*/
static void insert_freelist_front(void *bp);
static void remove_freelist(void *bp);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void) 
{

	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(8 * WSIZE)) == (void *)-1)
		return (-1);

	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */

	heap_listp += (2 * WSIZE);

	free_listp = heap_listp+(2*WSIZE);	//initializing free list pointer

	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */

	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (-1);

	return (0);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
	
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */

	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);
	
	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;

	else
		asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
	
	
	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	
	place(bp, asize);
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void
mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (!bp)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *
mm_realloc(void *ptr, size_t size)
{
		size_t old_size;
		void *newptr;
		size_t new_size;
	
		/* If size == 0 then this is just free, and we return NULL. */
		if (size== 0) {
		
			mm_free(ptr);
			return (NULL);

		}

		/* If oldptr is NULL, then this is just malloc. */
		else if (ptr == NULL)
			return (mm_malloc(size));

		old_size= GET_SIZE(HDRP(ptr));/* To store the size of block pointed by ptr*/
		new_size= size + 2*WSIZE;/*The size of new block including header and footer*/

		/*If requested size if not zero*/
		if(size>0){

			/*Not changing the block size if requested size is less than original size.*/
			if(new_size<=old_size)
				return ptr;

			else{
				size_t csize= old_size + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
				size_t asize;
				size_t nextalloc= GET_ALLOC(HDRP(NEXT_BLKP(ptr)));

				/* checking if the next block is not allocated and the size of the two blocks is greater than or equal the new size */
				if(!nextalloc && (csize>=new_size)){

					remove_freelist(NEXT_BLKP(ptr));

					PUT(HDRP(ptr),PACK(csize,1));

					PUT(FTRP(ptr),PACK(csize,1));	

					return ptr;	
				  }

				/*If next bloack is not allocated and it is the last block in heap and size of two blocks if less than new size*/
				else if(!nextalloc && ((GET_SIZE(HDRP(NEXT_BLKP(NEXT_BLKP(ptr)))))==0)){

					csize = new_size- (old_size+GET_SIZE(HDRP(NEXT_BLKP(ptr))));

					newptr = extend_heap(csize);

					asize = old_size + GET_SIZE(HDRP(newptr));

					PUT(HDRP(ptr),PACK(asize,1));

					PUT(FTRP(ptr),PACK(asize,1));

					return ptr;	
				}

				/*If the block to be reallocated is last block,so we exend the heap.*/
				else if(GET_SIZE(HDRP(NEXT_BLKP(ptr)))==0){

					csize=new_size-old_size;

					newptr = extend_heap(csize);

					asize = old_size + GET_SIZE(HDRP(newptr));

					PUT(HDRP(ptr),PACK(asize,1));

					PUT(FTRP(ptr),PACK(asize,1));

					return ptr;
				}

				/*If next block is not free and it is not the last block, we allocate a new block of requested size.*/
				else{

					newptr=mm_malloc(new_size);

					place(newptr,new_size);

					memcpy(newptr,ptr,new_size);

					mm_free(ptr);

					return newptr;
				}
			}
	}


	/* If realloc() fails the original block is left untouched  */
	else if(newptr==NULL){
		return NULL;
	}
}

/*
 * The following routines are for adding a free block to explicit linklist and removing an allocated block from linklist. 
 */

static void insert_freelist_front(void *bp){
	/*Setting the pointer of next block of bp to free_listp pointer*/
	SET_NEXT_PTR(bp,free_listp);
	
	/*Setting the pointer of previous block of free_listp to bp*/
	SET_PREV_PTR(free_listp,bp);

	/*Setting the pointer of previous block of bp to NULL*/
	SET_PREV_PTR(bp,NULL);

	/*Pointer to start of free list now points to bp.*/
	free_listp=bp;
}

static void remove_freelist(void *bp){
	
	/*if the pointer to previous block of bp is not null*/
	if (GET_PREV_PTR(bp)){
    	SET_NEXT_PTR(GET_PREV_PTR(bp), GET_NEXT_PTR(bp));
	}
	
	/*Set the pointer to first block of list to pointer to next block of bp*/
  	else{
    	free_listp = GET_NEXT_PTR(bp);
	}  
	
	/*Set the pointer to previous block of next block of bp to pointer of previous block of bp.*/
	SET_PREV_PTR(GET_NEXT_PTR(bp), GET_PREV_PTR(bp));

}
/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *coalesce(void *bp) 
{
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); 
	size_t size = GET_SIZE(HDRP(bp));

	if (prev_alloc && next_alloc) {                 /* Case 1- when both previous and next block are allocated */
	
		insert_freelist_front(bp);					

		return (bp);

	} else if (prev_alloc && !next_alloc) {         /* Case 2 -previous allocated and next not allocated*/
		
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));

		remove_freelist(NEXT_BLKP(bp));			

		PUT(HDRP(bp), PACK(size, 0));

		PUT(FTRP(bp), PACK(size, 0));
	} else if (!prev_alloc && next_alloc) {         /* Case 3 - next allocated and previous not allocated*/

		size += GET_SIZE(HDRP(PREV_BLKP(bp)));

		bp = PREV_BLKP(bp);		

		remove_freelist(bp);

		PUT(HDRP(bp), PACK(size, 0));

		PUT(FTRP(bp), PACK(size, 0));
	} else {                                        /* Case 4- both previous and next not allocated */

			size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 

		    GET_SIZE(FTRP(NEXT_BLKP(bp)));

		    remove_freelist(NEXT_BLKP(bp));

			remove_freelist(PREV_BLKP(bp));

		    bp=PREV_BLKP(bp);

			PUT(HDRP(bp), PACK(size, 0));

			PUT(FTRP(bp), PACK(size, 0));
		
	}
	
	insert_freelist_front(bp);
	return bp;
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *extend_heap(size_t words) 
{
	void *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */

	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */

	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	/* Coalesce if the previous block was free. */
	return (coalesce(bp));
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
 
static void *find_fit(size_t asize)
{
	void *bp;
	
	/*using first fit to traverse through explicit link list.*/
	for(bp=free_listp; GET_ALLOC(HDRP(bp))==0;bp=GET_NEXT_PTR(bp)){
		if(asize<=(size_t)GET_SIZE(HDRP(bp)))
			return bp;
	}

	/*No fit was found.*/
	return NULL;
}


/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 	
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   
	
	if ((csize - asize) >= (MINBLOCK)) { 

		PUT(HDRP(bp), PACK(asize, 1));

		PUT(FTRP(bp), PACK(asize, 1));

		remove_freelist(bp);        /*To remove the allocated block from freelists linklist*/

		bp = NEXT_BLKP(bp);

		PUT(HDRP(bp), PACK(csize - asize, 0));

		PUT(FTRP(bp), PACK(csize - asize, 0));

		coalesce(bp);
	} else {

		PUT(HDRP(bp), PACK(csize, 1));

		PUT(FTRP(bp), PACK(csize, 1));

		remove_freelist(bp);		/*To remove the allocated block from freelists linklist*/
	}
}

/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void checkblock(void *bp) 
{

	if ((uintptr_t)bp % DSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void checkheap(bool verbose){

	void *bp = heap_listp;
	if (verbose) 
	printf("Heap (%p):\n", heap_listp);

	if (((GET_SIZE(HDRP(heap_listp))) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
	printf("Bad prologue header\n");
	
	checkblock(heap_listp);
	
	/*Checking each block of freeblocks linklist.i.e checking each free block*/
	for (bp = free_listp; (GET_ALLOC(HDRP(bp))) == 0; bp = GET_NEXT_PTR(bp)){
		if (verbose)
		printblock(bp);
	
	checkblock(bp);
	}

	if(verbose)
		printblock(bp);

	if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))){
		printf("Bad epilogue header\n");
	}
}
/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */

static void
printblock(void *bp) 
{
	bool halloc, falloc;
	size_t hsize, fsize;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
	    hsize, (halloc ? 'a' : 'f'), 
	    fsize, (falloc ? 'a' : 'f'));
}
/*
 * The last lines of this file configures the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */
