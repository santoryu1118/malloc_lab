/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "week6_team6",
    /* First member's full name */
    "John Lee",
    /* First member's email address */
    "capjohnlee2@gmail.com",
    /* Second member's full name (leave blank if none) */
    "John Cena",
    /* Second member's email address (leave blank if none) */
    "johncena@wwc.com"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// MACROS
#define WSIZE 4            // word and header, footer size (bytes)
#define DSIZE 8            // double word sizes (bytes)
#define CHUNKSIZE (1<<12)  // extend heap by this amount

#define MAX(x,y) ((x) > (y) ?(x) :(y))              // max 
#define PACK(size, alloc)  ((size) | (alloc))       // size랑 bool allocated bit을 pack하는거
#define GET(p) (*(unsigned int*)(p))                // get_size, get_alloc에 쓰이는 함수
#define PUT(p, val) (GET(p) = (val))                // p address에 value 넣는거   PUT(HDRP(bp), PACK (size, 1)) 이런식으로
#define GET_SIZE(p) (GET(p) & ~0x7)                 // 16진수 7을 2진수로 바꾸면 111, ~111 == 000  alloc 3자리 bit 빼주는거
#define GET_ALLOC(p) (GET(p) & 0x1)                 // 할당되있는지 아닌지 보는 함수

#define HDRP(bp) ((char*)(bp) - WSIZE)                                // header의 address 
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)           // footer의 address 
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)))              // next node의 header의 address 
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(HDRP(bp)- WSIZE))       // prev node의 header의 address 

#define PRED_FREEP(bp)  (*(void**)(bp))             // *(GET(PRED_FREEP(bp))) == 다음 가용리스트의 bp //Predecessor
#define SUCC_FREEP(bp)  (*(void**)(bp + WSIZE))     // *(GET(SUCC_FREEP(bp))) == 다음 가용리스트의 bp //successor

// static variable
static char* heap_listp;
static char* next_findp;

// static functions
static void* extend_heap(size_t);
static void* coalesce(void*);
static void* find_fit(size_t);
static void* next_fit(size_t);
static void place(void*, size_t);


/* void *mem_sbrk(int incr); 함수는 커널의 brk 포인터에 incr을 더해서 힙을 늘리거나 줄인다. 
   실패시 (if ((incr < 0)|| (mem_brk + incr > mem_max_addr)) return -1 하고 성공시 return old_ptr값
*/

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void*)-1)
        return -1;
    PUT(heap_listp, 0);                           //alignment padding
    PUT(heap_listp + 1*WSIZE, PACK(DSIZE, 1));    //prologue header
    PUT(heap_listp + 2*WSIZE, PACK(DSIZE, 1));    //prologue footer
    PUT(heap_listp + 3*WSIZE, PACK(0, 1));        //epilogue header
    heap_listp += 2*WSIZE;
    next_findp = heap_listp;

    // Extend the empty heap with a free block of CHUNKSIZE bytes (초기 가용 블록 생성)
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

static void* extend_heap(size_t n_words)
{
    char *bp;
    size_t asize;

    // allocate an even number of words to maintain alignment
    asize = (n_words % 2) ? (n_words +1) * WSIZE : n_words * WSIZE;
    if ((long)(bp = mem_sbrk(asize)) == -1)
        return NULL;
    
    PUT(HDRP(bp), PACK(asize, 0));  // free block header
    PUT(FTRP(bp), PACK(asize, 0));  // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  // new epilogue header

    // coalesce if necessary
    return coalesce(bp);
}

static void* coalesce(void * bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  // 앞의 block의 footer을 확인
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));  // 뒤의 block의 header를 확인 
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){  // if prev & next are both allocated
        next_findp = bp;
        return bp;
    }
    
    else if (prev_alloc && !next_alloc){        // 다음 block만 free면
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  // next block의 header에서 size 받아와서 더해줌
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));           // FTRP는 GET_SIZE(HDRP(bp))를 이용하기 때문에 FTRP(bp)가 next block의 footer을 가르킬거임
    }

    else if (!prev_alloc && next_alloc){           // 전 block만 free면
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));     // previous block의 footer에서 size 받아와서 더해줌
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else{       // prev & next 둘다 free 라면
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    next_findp = bp;
    return bp;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 * Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size){
    size_t asize;    //adjusted block size
    char* bp;

    if (size == 0)
        return NULL;
    
    if (size <= DSIZE)
        asize = 2*DSIZE;   //최소 16byte의 블록 구성
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/ DSIZE);
    
    // search the free list for a fit
    if ((bp = next_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    // if there aren't appropriate space left and have to extend the heap
    size_t extendsize;
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

// mm_malloc 함수에서 size와 boolean alloc을 확인하는 helper function
// first fit으로 처음부터 검색
static void* find_fit(size_t asize){
    void* bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) >0 ; bp = NEXT_BLKP(bp)){
        // 만약 size도 맞고 allocation도 안되있으면
        if (GET_SIZE(HDRP(bp)) >= asize && !GET_ALLOC(HDRP(bp)))
            return bp;
    }
    return NULL;
}

// next fit으로 전에 검색 종료된 부분부터 검색
static void* next_fit(size_t asize){
    // next_findp = heap_listp;
    void* bp = next_findp;
    
    while (GET_SIZE(HDRP(next_findp)) > 0){
        if (GET_SIZE(HDRP(next_findp)) >= asize && !GET_ALLOC(HDRP(next_findp))){
            return next_findp;
        }
        next_findp = NEXT_BLKP(next_findp);
    }

    next_findp = heap_listp;
    while(GET_SIZE(HDRP(next_findp)) > 0 && next_findp < bp){
        if (GET_SIZE(HDRP(next_findp)) >= asize && !GET_ALLOC(HDRP(next_findp))){
            return next_findp;
        }
        next_findp = NEXT_BLKP(next_findp);
    }
    return NULL;
}


// mm_malloc 함수에서 heap에 할당하는 helper function
static void place(void* bp, size_t asize){

    size_t csize = GET_SIZE(HDRP(bp));

    // 만약 사이즈가 커서 split을 할 정도라면
    if (csize >= asize + 2*DSIZE){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    // free the particular block
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // coalesce any free blocks and merge them
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * realloc은 이미 할당한 블록의 크기를 바꿀 때 사용
 * 인자로 주어진 사이즈가 기존 블록의 사이즈보다 작으면 인자로 주어진 사이즈만큼의 데이터만 잘라서 옮긴다.
 * memcpy는 블록 내 데이터를 옮기는 기본 제공 함수
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}


