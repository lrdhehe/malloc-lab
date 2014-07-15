/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * hbovik - Harry Bovik
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  Blocks are never coalesced or reused.  The size of
 * a block is found at the first aligned word before the block (we need
 * it for realloc).
 *
 * This code is correct and blazingly fast, but very bad usage-wise since
 * it never frees anything.
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"


// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                             printf("Checkheap failed on line %d\n", __LINE__);\
                             exit(-1);  \
                        }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ //line:vm:mm:beginconst
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */  //line:vm:mm:endconst

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    //line:vm:mm:put

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //line:vm:mm:ftrp

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //line:vm:mm:nextblkp
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //line:vm:mm:prevblkp

/*Put and read pred and succ free address to the block*/
#define PUTPRE(p,prep) (PUT(p,(int)((char*)(prep)-(char*)(heap_listp))))
#define PUTSUC(p,sucp) (PUT((p+WSIZE),(int)((char*)(sucp)-(char*)(heap_listp))))
#define GETPRE(p)      ((char*)(GET(p)+(char*)(heap_listp)))
#define GETSUC(p)      ((char*)(GET(p+WSIZE)+(char*)(heap_listp)))
/* $end mallocmacros */


/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);
static void addfreeblock(void *bp);
static void printdata(int start);

static char *heap_listp = 0;  /* Pointer to first block */
/*
 * mm_init - Called when a new trace starts.
 */
/* $begin mminit */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(8*WSIZE)) == (void *)-1) //line:vm:mm:begininit
	return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(2*DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), 0);             // put pre address == 0
    PUT(heap_listp + (3*WSIZE), 16);            //put success address = end block
    PUT(heap_listp + (4*WSIZE), PACK(2*DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));     /* Epilogue header */
    PUT(heap_listp + (6*WSIZE), 0);     /* Epilogue header */
    PUT(heap_listp + (7*WSIZE), 0);     /* Epilogue header */
    heap_listp += (2*WSIZE);                     //line:vm:mm:endinit
/* $end mminit */
/* $begin mminit */

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
	return -1;
	//printf("INIT finish\n");
	//printdata(0);
    return 0;
}
/* $end mminit */

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
/* $begin mmmalloc */
void *malloc(size_t size)
{
    //printf("malloc %d\n",size);
    //printdata(0);
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

/* $end mmmalloc */
    if (heap_listp == 0){
	mm_init();
    }
/* $begin mmmalloc */
    /* Ignore spurious requests */
    if (size == 0)
	return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)                                          //line:vm:mm:sizeadjust1
	asize = 2*DSIZE;                                        //line:vm:mm:sizeadjust2
    else
	asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); //line:vm:mm:sizeadjust3

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  //line:vm:mm:findfitcall
	place(bp, asize);                  //line:vm:mm:findfitplace
	return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                 //line:vm:mm:growheap1
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
	return NULL;                                  //line:vm:mm:growheap2
    place(bp, asize);
   // printf("Malloc finish\n");
    //printdata(0);
    return bp;
}
/* $end mmmalloc */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words)
{
    //printdata("extend heap\n");
    //printdata(0);
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; //line:vm:mm:beginextend
    if ((long)(bp = mem_sbrk(size)) == -1)
	return NULL;


    bp-=2*WSIZE;
    char *endblock = GETPRE(bp);

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   //line:vm:mm:freeblockhdr
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   //line:vm:mm:freeblockftr
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ //line:vm:mm:newepihdr
  /*  PUTSUC(bp,NEXT_BLKP(bp));
    PUTPRE(NEXT_BLKP(bp),bp);
    PUTSUC(NEXT_BLKP(bp),heap_listp);
    */
    PUTSUC(endblock,NEXT_BLKP(bp));
    PUTPRE(NEXT_BLKP(bp),endblock);
    PUTSUC(NEXT_BLKP(bp),heap_listp);

    /* Coalesce if the previous block was free */
    char* result = coalesce(bp);
    //printf("END extend heap\n");
    //printdata(0);
    return result;
}
/* $end mmextendheap */


/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
/* $begin mmfree */
void free(void *bp)
{
    //printf("free %ld\n",(char*)(bp)-heap_listp);
    //printdata(0);
/* $end mmfree */
    if(bp == 0)
	return;

/* $begin mmfree */
    size_t size = GET_SIZE(HDRP(bp));
/* $end mmfree */
    if (heap_listp == 0){
	mm_init();
    }
/* $begin mmfree */

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* $end mmfree */

static void *coalesce(void *bp)
{
    //printf("coalesce %ld\n",(char*)(bp)-heap_listp);
    //printdata(0);
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    char* pre = PREV_BLKP(bp);
    char* suc = NEXT_BLKP(bp);
    if (prev_alloc && next_alloc) {            /* Case 1 */
    addfreeblock(bp);
	return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size,0));
    PUTPRE(bp,GETPRE(suc));
    PUTSUC(GETPRE(suc),bp);
	PUTSUC(bp,GETSUC(suc));
	PUTPRE(GETSUC(suc),bp);
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
	size += GET_SIZE(HDRP(PREV_BLKP(bp)));
	PUT(FTRP(bp), PACK(size, 0));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);
    }

    else {                                     /* Case 4 */
	size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
	    GET_SIZE(FTRP(NEXT_BLKP(bp)));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
	PUTSUC(pre,GETSUC(suc));
	PUTPRE(GETSUC(suc),pre);
	bp = PREV_BLKP(bp);
    }
    //printf("end coalesce\n");
    //printdata(0);
    return bp;
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.  I'm too lazy
 *      to do better #SWAG
 */
void *realloc(void *ptr, size_t size)
{
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
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    mm_free(ptr);

    return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
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
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
     /* $end mmplace-proto */
{
    //printf("place %ld, size = %ld\n",(char*)(bp)-heap_listp,asize);
    //printdata(0);
    size_t csize = GET_SIZE(HDRP(bp));
    char* pre = GETPRE(bp);
    char* suc = GETSUC(bp);
    if ((csize - asize) >= (2*DSIZE)) {//??????QUESTION
	PUT(HDRP(bp), PACK(asize, 1));
	PUT(FTRP(bp), PACK(asize, 1));
	bp = NEXT_BLKP(bp);
	PUT(HDRP(bp), PACK(csize-asize, 0));
	PUT(FTRP(bp), PACK(csize-asize, 0));
	PUTSUC(pre,bp);
	PUTPRE(bp,pre);
	PUTSUC(bp,suc);
	PUTPRE(suc,bp);
    }
    else {
	PUT(HDRP(bp), PACK(csize, 1));
	PUT(FTRP(bp), PACK(csize, 1));
	PUTSUC(pre,suc);
	PUTPRE(suc,pre);
    }
    //printf("end place\n");
    //printdata(0);
}
/* $end mmplace */


/*
 * find_fit - Find a fit for a block with asize bytes
 */
/* $begin mmfirstfit */
/* $begin mmfirstfit-proto */
static void *find_fit(size_t asize)
/* $end mmfirstfit-proto */
{
    /* First fit search */
    void *bp;//=GETSUC(heap_listp);
    void *first = 0;
    int flag = 0;

    for (bp = GETSUC(heap_listp); GET_SIZE(HDRP(bp)) > 0; bp = GETSUC(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            //printf("Find address %d\n",(char*)(bp)-heap_listp);
            if(flag ==0 )
            {
                flag = 1;
                first = bp;
                continue;
            }
            return bp;
        }
    }
    if(flag == 1)
    {
        return first;
    }


    return NULL; /* No fit */
}

static void printblock(void *bp)
{
    size_t hsize, halloc, fsize, falloc;

    checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if (hsize == 0) {
	printf("%p: EOL\n", bp);
	return;
    }

    /*  printf("%p: header: [%p:%c] footer: [%p:%c]\n", bp,
	hsize, (halloc ? 'a' : 'f'),
	fsize, (falloc ? 'a' : 'f')); */
}
static void addfreeblock(void *bp)
{
    //printf("ADD free block%d\n",(char*)(bp)-heap_listp);
    char* p = heap_listp;
    while(GETSUC(p)<(char*)(bp))
    {
        p = GETSUC(p);
    }
    char* suc = GETSUC(p);
    PUTSUC(p,bp);
    PUTPRE(bp,p);
    PUTSUC(bp,suc);
    PUTPRE(suc,bp);
    //printf("End addfree block\n");
    //printdata(0);

}
static void printdata(int start)
{
    return;
    char *bp = heap_listp+start;
    while(GET_SIZE(HDRP(bp))>0)
    {
    /*
        printf("address = %d,",bp-heap_listp);
        printf("alloc = %d,", GET_ALLOC(HDRP(bp)));
        printf("size = %d,",GET_SIZE(HDRP(bp)));
        if(!GET_ALLOC(HDRP(bp)))
        {
            printf("pre addr = %d, succes addr = %d",GETPRE(bp)-heap_listp,GETSUC(bp)-heap_listp);
        }
        printf("\n");
        */
        bp = NEXT_BLKP(bp);
    }
    /*
    printf("address = %d,",bp-heap_listp);
    printf("alloc = %d,", GET_ALLOC(HDRP(bp)));
    printf("size = %d,",GET_SIZE(HDRP(bp)));
    printf("pre addr = %d, succes addr = %d",GETPRE(bp)-heap_listp,GETSUC(bp)-heap_listp);
    printf("\n");
    printf("end address = %d\n",bp-heap_listp);
    */
}


/*
 * mm_checkheap - There are no bugs in my code, so I don't need to check,
 *      so nah!
 */
int mm_checkheap(int verbose){
	/*Get gcc to be quiet. */
	verbose = verbose;
    return 0;
}
