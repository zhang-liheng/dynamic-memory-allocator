/*
 *
 * mm.c
 *
 *
 * Name: Zhang Liheng
 * Student ID: 2200013214
 *
 *
 * This is a dynamic memory allocator.
 * Free block organization: segregated ordered free lists
 *                          each is an explicit free list without footers
 * Placement policy:        first fit in ordered lists, equivalent to best fit
 * Coalecsing policy:       immediate coalecsing
 *
 *
 *
 *
 *
 * The layout of the heap:
 * --------------------------------------------------------------------------
 * | head1 | head2 | ... | headk | (padding) | prologue | blocks | epilogue |
 * --------------------------------------------------------------------------
 * |                                               |             |         |
 * mem_heap_lo()                          heap_listp      epilogue mem_heap_hi()
 * class_head
 *
 * k is the number of size classes, CLASS_NUM.
 * The ith class links blocks with size between pow(2, i+3) to pow(2, i+4)
 * Each header is a 4-byte offset relative to heap_listp.
 *
 *
 *
 *
 *
 * The layout of an allocated block:
 * ----------------------------------------------
 * |    header    |   payload   |   (padding)   |
 * ----------------------------------------------   At least 16 bytes
 *      4 bytes   |
 *                bp
 *
 *
 *
 *
 *
 * The layout of an allocated block header:
 * --------------------------------------------------
 * |    size    |   0   |   prev_alloc  |   alloc   |
 * --------------------------------------------------
 *                     second-to-last bit   last bit
 *
 * The prev_alloc bit indicates whether previous block is allocated or not.
 *
 *
 *
 *
 *
 * The layout of a free block:
 * ------------------------------------------------------
 * |    header    |   pred   |   succ   |...|   footer  |
 * ------------------------------------------------------   At least 16 bytes
 *      4 bytes   |  4 bytes    4 bytes             4 bytes
 *                bp
 *
 * The layout of its header/footer is identical to the allocated block header.
 * The pred field stores the offset of the block pointer of its predecessor
 * relative to heap_listp.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
// #define DEBUG
#ifdef DEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define CHECK(lineno) mm_checkheap(lineno)
#define PRINT() print_heap()
#else
#define dbg_printf(...)
#define CHECK(lineno)
#define PRINT()
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT - 1)) & ~0x7)

/* Constants and macros */
#define WSIZE 4             /* word size (bytes) */
#define DSIZE 8             /* double word size (bytes) */
#define CHUNKSIZE (1 << 11) /* Extend heap by this amount (bytes) */
#define INITSIZE (1 << 11)  /* initialize heap by this amount (bytes) */
#define CLASS_NUM 12        /* number of size classes */

#define PREV_ALLOCATED 2 /* previous block is allocated */
#define PREV_FREE 0      /* previous block is free */
#define ALLOCATED 1      /* current block is allocated */
#define FREE 0           /* current block is free */

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

/* Pack a size and allocated bits into a word */
#define PACK(size, prev_alloc, alloc) ((size) | (prev_alloc) | (alloc))

/* Read a word at address p */
#define GET(p) (*(unsigned int *)(p))
/* Write a word at address p */
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
/* Read previous allocated bit from address p */
#define GET_PREV_ALLOC(p) (GET(p) & 0x2)
/* Read allocated bit from address p */
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header */
#define HDRP(bp) ((char *)(bp)-WSIZE)
/* Given block ptr bp, compute address of its footer */
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
/* Given block ptr bp, compute address of its pred field */
#define PREDP(bp) ((char *)(bp))
/* Given block ptr bp, compute address of its succ field */
#define SUCCP(bp) ((char *)(bp) + WSIZE)

/* Given block ptr bp, compute address of next block */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
/* Given block ptr bp, compute address of previous block */
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))
/* Given block ptr bp, compute address of its predecessor */
#define PRED_BLKP(bp) ((long)GET(PREDP(bp)) + heap_listp)
/* Given block ptr bp, compute address of its successor */
#define SUCC_BLKP(bp) ((long)GET(SUCCP(bp)) + heap_listp)

/* Address/offset conversion */
#define A2O(bp) ((unsigned int)((char *)bp - heap_listp))
/* Offset/address conversion */
#define O2A(off) ((long)off + heap_listp)

/* Global variables */
/* ptr to prologue */
static char *heap_listp = 0;
/* ptr to start address of segretated free lists */
static char *class_head = 0;

/* Helper routines */
static inline void *extend_heap(size_t words);
static inline void *coalesce(void *bp);
static inline void *get_class_ptr(void *bp);
static inline void del_free_list(void *bp);
static inline void add_free_list(void *bp);
static inline void *find_fit(size_t asize);
static inline void place(void *bp, size_t asize);
static void print_heap(void);

/*
 * mm_init - initialize the memory
 * return -1 on error, 0 on success.
 */
int mm_init(void)
{
    dbg_printf("\ninit\n");

    /* initialize global variables */
    heap_listp = 0;
    class_head = 0;

    /* allocate heap with headers, possible padding, prologue and epilogue */
    int padding = CLASS_NUM % 2 ? 0 : 1;
    class_head = mem_sbrk((CLASS_NUM + padding + 3) * WSIZE);
    if (class_head == (void *)-1)
        return -1;

    /* header points to heap_listp at start */
    memset(class_head, 0, CLASS_NUM * WSIZE);

    heap_listp = class_head + (CLASS_NUM + padding) * WSIZE;
    /* prologue header */
    PUT(heap_listp, PACK(DSIZE, PREV_ALLOCATED, ALLOCATED));
    /* prologue padding */
    PUT(heap_listp + 1 * WSIZE, 0);
    /* epilogue header */
    PUT(heap_listp + 2 * WSIZE, PACK(0, PREV_ALLOCATED, ALLOCATED));

    /* finally set the value of heap_listp */
    heap_listp += 1 * WSIZE;

    /* extend heap, add it to free lists and set the value of epilogue */
    void *bp = extend_heap(INITSIZE / WSIZE);
    if (bp == NULL) /* fail */
        return -1;

    return 0;
}

/*
 * malloc - Allocate a block with at least size bytes of payload
 * return NULL on error, block ptr on success.
 */
void *malloc(size_t size)
{
    dbg_printf("\nmalloc %lu\n", size);

    size_t asize, extendsize;
    void *bp;
    if (heap_listp == 0)
        mm_init();

    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= 3 * WSIZE)
        asize = 4 * WSIZE;
    else
        asize = DSIZE * ((size + (WSIZE) + (DSIZE - 1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
    }
    else
    {
        extendsize = MAX(asize, CHUNKSIZE);
        bp = extend_heap(extendsize / WSIZE);
        if (bp == NULL)
            return NULL;
        place(bp, asize);
    }

    dbg_printf("after malloc:\n");
    PRINT();

    return bp;
}

/*
 * free - free a block
 */
void free(void *bp)
{
    dbg_printf("\nfree: %u", A2O(bp));

    unsigned int size, next_size, next_alloc;

    if (!bp)
        return;

    size = GET_SIZE(HDRP(bp));
    if (!heap_listp)
        mm_init();

    /* set header and footer of this block*/
    unsigned int prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    PUT(HDRP(bp), PACK(size, prev_alloc, FREE));
    PUT(FTRP(bp), PACK(size, prev_alloc, FREE));

    /* set header (and footer) of next block */
    next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
    next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(next_size, PREV_FREE, next_alloc));
    if (!next_alloc)
        PUT(FTRP(NEXT_BLKP(bp)), PACK(next_size, PREV_FREE, next_alloc));

    bp = coalesce(bp);

    dbg_printf("after free:\n");
    PRINT();
}

/*
 * realloc - reallocte the old block
 * uses the old block and next free block if possible.
 * returns NULL on error, block ptr on success.
 */
void *realloc(void *oldbp, size_t size)
{
    dbg_printf("\nrealloc: %u, %lu\n", A2O(oldbp), size);

    /* If size == 0 then this is just free. */
    if (size == 0)
    {
        mm_free(oldbp);

        dbg_printf("after realloc:\n");
        PRINT();

        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if (oldbp == NULL)
    {
        void *ret = mm_malloc(size);

        dbg_printf("after realloc:\n");
        PRINT();

        return ret;
    }

    size_t oldsize, freesize = 0, asize;
    unsigned int prev_alloc = GET_PREV_ALLOC(HDRP(oldbp));
    void *newbp, *freebp, *nextbp;

    /* the size of this block */
    oldsize = GET_SIZE(HDRP(oldbp));

    /* the size of next block if it is free */
    if (!GET_ALLOC(HDRP(NEXT_BLKP(oldbp))))
        freesize = GET_SIZE(HDRP(NEXT_BLKP(oldbp)));

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= 3 * WSIZE)
        asize = 4 * WSIZE;
    else
        asize = DSIZE * ((size + (WSIZE) + (DSIZE - 1)) / DSIZE);

    /* need not copy */
    if (oldsize + freesize >= asize)
    {
        /* should split */
        if (oldsize + freesize >= asize + (2 * DSIZE))
        {
            if (freesize)
                del_free_list(NEXT_BLKP(oldbp));

            /* set header of this block */
            PUT(HDRP(oldbp), PACK(asize, prev_alloc, ALLOCATED));

            /* set header and footer of next free block */
            freebp = NEXT_BLKP(oldbp);
            PUT(HDRP(freebp),
                PACK(oldsize + freesize - asize, PREV_ALLOCATED, FREE));
            PUT(FTRP(freebp),
                PACK(oldsize + freesize - asize, PREV_ALLOCATED, FREE));
            add_free_list(freebp);

            /* if at first the next block is allocated,
                the prev_alloc bit of its header should be changed now! */
            if (!freesize)
            {
                nextbp = NEXT_BLKP(freebp);
                unsigned int next_size = GET_SIZE(HDRP(nextbp));
                unsigned int next_alloc = GET_ALLOC(HDRP(nextbp));
                PUT(HDRP(nextbp), PACK(next_size, PREV_FREE, next_alloc));
            }
        }
        /* should not split */
        else
        {
            if (freesize)
                del_free_list(NEXT_BLKP(oldbp));
            PUT(HDRP(oldbp), PACK(oldsize + freesize, prev_alloc, ALLOCATED));

            if (freesize)
            {
                nextbp = NEXT_BLKP(oldbp);
                unsigned int next_size = GET_SIZE(HDRP(nextbp));
                unsigned int next_alloc = GET_ALLOC(HDRP(nextbp));
                PUT(HDRP(nextbp), PACK(next_size, PREV_ALLOCATED, next_alloc));
            }
        }

        dbg_printf("after realloc:\n");
        PRINT();

        return oldbp;
    }
    /* need copy */
    else
    {
        newbp = mm_malloc(asize);

        /* If realloc() fails the original block is left untouched. */
        if (!newbp)
            return 0;

        /* Copy the old data. */
        if (size < oldsize)
            oldsize = size;
        memcpy(newbp, oldbp, oldsize);

        /* Free the old block. */
        mm_free(oldbp);

        dbg_printf("after realloc:\n");
        PRINT();

        return newbp;
    }
}

/*
 * calloc - malloc & set the memory all-zero
 * return NULL on error, block ptr on success.
 */
void *calloc(size_t nmemb, size_t size)
{
    size_t bytes = nmemb * size;
    void *bp = malloc(bytes);

    memset(bp, 0, bytes);

    return bp;
}

/*
 * Return whether the pointer is in the heap.
 */
static int in_heap(const void *p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 */
static int aligned(const void *p)
{
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap - check almost everything
 */
void mm_checkheap(int lineno)
{
    dbg_printf("\nin check_heap\n");
    if (GET(heap_listp - WSIZE) != PACK(DSIZE, PREV_ALLOCATED, ALLOCATED))
    {
        printf("Error: line %d, invalid prologue %u\n",
               lineno, GET(heap_listp - WSIZE));
        exit(0);
    }

    if ((GET(mem_heap_hi() - 3) & ~0x2) != PACK(0, PREV_FREE, ALLOCATED))
    {
        printf("Error: line %d, invalid epilogue %u\n", lineno, GET(mem_heap_hi() - 3));
        exit(0);
    }

    /* check blocks one by one */
    char *prev_bp = 0;
    int heap_free_cnt = 0, list_free_cnt = 0;
    for (char *bp = heap_listp; bp < (char *)mem_heap_hi();
         prev_bp = bp, bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)))
        {
            heap_free_cnt++;
        }

        if (!aligned(bp))
        {
            printf("Error: line %d, unaligned block (%u; %u)\n",
                   lineno, A2O(HDRP(bp)),
                   A2O(HDRP(bp) + GET_SIZE(HDRP(bp)) - 1));
            print_heap();
            exit(0);
        }

        if (!in_heap(HDRP(bp)) || !in_heap(HDRP(bp) + GET_SIZE(HDRP(bp)) - 1))
        {
            printf("Error: line %d, block (%u; %u) outside heap (%u; %u)\n ",
                   lineno,
                   A2O(HDRP(bp)), A2O(HDRP(bp) + GET_SIZE(HDRP(bp)) - 1),
                   A2O(mem_heap_lo()), A2O(mem_heap_hi()));
            print_heap();
            exit(0);
        }

        if (bp != heap_listp && GET_SIZE(HDRP(bp)) < 2 * DSIZE)
        {
            printf("Error: line %d, block size too small (%u; %u)\n",
                   lineno, A2O(HDRP(bp)),
                   A2O(HDRP(bp) + GET_SIZE(HDRP(bp)) - 1));
            print_heap();
            exit(0);
        }

        if (prev_bp &&
            GET_ALLOC(HDRP(prev_bp)) != (GET_PREV_ALLOC(HDRP(bp)) >> 1))
        {
            printf("Error: line %d, inconsistent alloc bit.\n", lineno);
            printf("Prev header %u alloc %u cur header %u prev_alloc %u\n",
                   A2O(HDRP(prev_bp)), GET_ALLOC(HDRP(prev_bp)),
                   A2O(HDRP(bp)), (GET_PREV_ALLOC(HDRP(bp)) >> 1));
            print_heap();
            exit(0);
        }

        if (!GET_ALLOC(HDRP(bp)) && GET_ALLOC(FTRP(bp)))
        {
            printf("Error: line %d, inconsistent alloc bit in free (%u; %u)\n",
                   lineno, A2O(HDRP(bp)),
                   A2O(HDRP(bp) + GET_SIZE(HDRP(bp)) - 1));
            print_heap();
            exit(0);
        }

        if (prev_bp && !GET_ALLOC(HDRP(prev_bp)) && !GET_ALLOC(HDRP(bp)))
        {
            printf("Error: line %d, contiguous free blocks (%u; %u)\n",
                   lineno, A2O(HDRP(bp)),
                   A2O(HDRP(bp) + GET_SIZE(HDRP(bp)) - 1));
            print_heap();
            exit(0);
        }
    }

    /* check blocks in free lists */
    for (int no = 0; no < CLASS_NUM; no++)
    {
        prev_bp = 0;
        for (char *bp = O2A(GET(class_head + no * WSIZE)); A2O(bp);
             list_free_cnt++, prev_bp = bp, bp = SUCC_BLKP(bp))
        {
            if (prev_bp)
            {
                if (PRED_BLKP(bp) != prev_bp)
                {
                    printf("Error: line %d, inconsistent pred and succ.\n",
                           lineno);
                    print_heap();
                    exit(0);
                }
            }

            if (!in_heap(bp))
            {
                printf("Error: line %d, block (%u; %u) outside heap (%u; %u)\n",
                       lineno,
                       A2O(HDRP(bp)), A2O(HDRP(bp) + GET_SIZE(HDRP(bp)) - 1),
                       A2O(mem_heap_lo()), A2O(mem_heap_hi()));
                print_heap();
                exit(0);
            }
        }
    }

    /* check free block consistency */
    if (heap_free_cnt != list_free_cnt)
    {
        printf("Error: line %d, inconsistent free counts.\n", lineno);
        printf("heap: %d, list: %d\n", heap_free_cnt, list_free_cnt);
        print_heap();
        exit(0);
    }
}

/**
 * Helper routines
 */
/*
 * extend_heap - extend heap by words*WSIZE bytes, set headers/footers
 * accordingly, and coalesce the free block.
 * returns NULL on error, (coalesced) free block ptr at success.
 */
static inline void *extend_heap(size_t words)
{
    char *bp;
    unsigned int prev_alloc;
    /* Allocate an even number of words to maintain alignment */
    size_t size = size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    PUT(HDRP(bp), PACK(size, prev_alloc, FREE));
    PUT(FTRP(bp), PACK(size, prev_alloc, FREE));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, PREV_FREE, ALLOCATED));

    /* Coalesce if the previous block was free, and add it to free list */
    return coalesce(bp);
}

/**
 * coalesce - coalesce the prev/next blocks if possible
 * returns (coalesced) frree block ptr.
 * NOTES:
 * This function is in charge of maintaining free lists.
 */
static inline void *coalesce(void *bp)
{
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    /* Case 1: previous and next blocks are allocated */
    if (prev_alloc && next_alloc)
    {
        add_free_list(bp);
        return bp;
    }
    /* Case 2: next block is free */
    else if (prev_alloc && !next_alloc)
    {
        del_free_list(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, prev_alloc, FREE));
        PUT(FTRP(bp), PACK(size, prev_alloc, FREE));

        add_free_list(bp);
    }
    /* Case 3: previous block is free */
    else if (!prev_alloc && next_alloc)
    {
        del_free_list(PREV_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        prev_alloc = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));

        PUT(FTRP(bp), PACK(size, prev_alloc, FREE));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, prev_alloc, FREE));
        bp = PREV_BLKP(bp);

        add_free_list(bp);
    }
    /* Case 4: previous and next blocks are free */
    else
    {
        del_free_list(PREV_BLKP(bp));
        del_free_list(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        prev_alloc = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));

        PUT(HDRP(PREV_BLKP(bp)), PACK(size, prev_alloc, FREE));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, prev_alloc, FREE));
        bp = PREV_BLKP(bp);

        add_free_list(bp);
    }

    return bp;
}

/*
 * get_class_ptr - get ptr to the header of the right list
 */
static inline void *get_class_ptr(void *bp)
{
    unsigned int size = GET_SIZE(HDRP(bp));
    size >>= 5;
    unsigned int i = 0;
    while (size && i < CLASS_NUM - 1)
    {
        ++i;
        size >>= 1;
    }
    return class_head + i * WSIZE;
}

/*
 * del_free_list - delete a free block from list
 */
static inline void del_free_list(void *bp)
{
    void *pred_bp = PRED_BLKP(bp);
    void *succ_bp = SUCC_BLKP(bp);
    if (pred_bp == heap_listp)
    {
        void *cp = get_class_ptr(bp);
        PUT(cp, A2O(SUCC_BLKP(bp)));
    }
    else
    {
        PUT(SUCCP(pred_bp), A2O(SUCC_BLKP(bp)));
    }
    if (succ_bp != heap_listp)
    {
        PUT(PREDP(succ_bp), A2O(PRED_BLKP(bp)));
    }
}

/*
 * add_free_list - insert a free block to the right ordered list
 */
static inline void add_free_list(void *bp)
{
    void *cp = get_class_ptr(bp);
    if (!GET(cp)) /* list is empty */
    {
        PUT(cp, A2O(bp));
        PUT(PREDP(bp), 0);
        PUT(SUCCP(bp), 0);
    }
    else
    {
        void *cur_bp = O2A(GET(cp));
        void *succ_bp = SUCC_BLKP(cur_bp);
        unsigned int size = GET_SIZE(bp);
        while (succ_bp != heap_listp && GET_SIZE(succ_bp) < size)
        {
            cur_bp = succ_bp;
            succ_bp = SUCC_BLKP(succ_bp);
        }
        PUT(SUCCP(cur_bp), A2O(bp));
        PUT(PREDP(bp), A2O(cur_bp));
        PUT(SUCCP(bp), A2O(succ_bp));
        if (succ_bp != heap_listp)
        {
            PUT(PREDP(succ_bp), A2O(bp));
        }
    }
}

/**
 * find_fit - find a block to allocate.
 * returns NULL on fail, block ptr on success.
 */
static inline void *find_fit(size_t asize)
{
    void *cp, *bp;
    size_t size = asize;
    size >>= 5;
    unsigned int i = 0;
    while (size && i < CLASS_NUM - 1)
    {
        ++i;
        size >>= 1;
    }

    while (i < CLASS_NUM)
    {
        cp = class_head + i * WSIZE; /* current class being searched */
        if (GET(cp))
        {
            bp = O2A(GET(cp));
            while (bp != heap_listp && GET_SIZE(HDRP(bp)) < asize)
            {
                bp = SUCC_BLKP(bp);
            }
            if (bp != heap_listp) /* found */
            {
                return bp;
            }
        }
        i++;
    }
    return NULL;
}

/**
 * place - place a block, possibly splitting it.
 */
static inline void place(void *bp, size_t asize)
{
    unsigned int csize = GET_SIZE(HDRP(bp));

    del_free_list(bp);

    /* need split */
    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, PREV_ALLOCATED, ALLOCATED));

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, PREV_ALLOCATED, FREE));
        PUT(FTRP(bp), PACK(csize - asize, PREV_ALLOCATED, FREE));

        add_free_list(bp);
    }
    /* should not split */
    else
    {
        PUT(HDRP(bp), PACK(csize, PREV_ALLOCATED, ALLOCATED));

        unsigned int next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(next_size, PREV_ALLOCATED, ALLOCATED));
    }
}

/*
 * print_heap - print the heap structure. For debug purpose.
 */
static void print_heap(void)
{
    void *bp;
    int cnt = 0;
    for (bp = heap_listp; bp < mem_heap_hi(); bp = NEXT_BLKP(bp), cnt++)
    {
        printf("block %d:\t", cnt);
        printf("size %u\t", GET_SIZE(HDRP(bp)));
        printf("prev_alloc %u\t", GET_PREV_ALLOC(HDRP(bp)));
        printf("alloc %u\t", GET_ALLOC(HDRP(bp)));
        printf("offset (%u; %u)\t", A2O(HDRP(bp)), A2O(HDRP(bp) + GET_SIZE(HDRP(bp)) - 1));
        if (!GET_ALLOC(HDRP(bp)))
        {
            printf("pred %u\t", GET(PREDP(bp)));
            printf("succ %u\t", GET(SUCCP(bp)));
            printf("footer\t");
            printf("size %u\t", GET_SIZE(FTRP(bp)));
            printf("prev_alloc %u\t", GET_PREV_ALLOC(FTRP(bp)));
            printf("alloc %u\t", GET_ALLOC(FTRP(bp)));
        }
        printf("\n");
    }
    printf("block %d:\t", cnt);
    printf("size %u\t", GET_SIZE(HDRP(bp)));
    printf("prev_alloc %u\t", GET_PREV_ALLOC(HDRP(bp)));
    printf("alloc: %u\t", GET_ALLOC(HDRP(bp)));
    printf("offset: (%u; %u)\t", A2O(HDRP(bp)), A2O(HDRP(bp) + 3));
    printf("\n");
    return;
}