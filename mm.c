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

#define MAX(x,y) ((x) > (y) ?(x) :(y))              // max 함수
#define PACK(size, alloc)  ((size) | (alloc))       // size랑 bool allocated bit을 pack하는거
#define GET(p) (*(unsigned int*)(p))                // put, get_size, get_alloc에 쓰이는 함수, p pointer가 가리키는 value (block의 size, alloc)
#define PUT(p, val) (GET(p) = (val))                // p address에 value 넣는거   PUT(HDRP(bp), PACK (size, 1)) 이런식으로
#define GET_SIZE(p) (GET(p) & ~0x7)                 // 16진수 7을 2진수로 바꾸면 111, ~111 == 000  alloc 3자리 bit 빼주는거
#define GET_ALLOC(p) (GET(p) & 0x1)                 // 할당되있는지 아닌지 보는 함수

#define HDRP(bp) ((char*)(bp) - WSIZE)                                // header의 address 
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)           // footer의 address 
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)))              // next node의 header의 address 
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(HDRP(bp)- WSIZE))       // prev node의 header의 address 

#define PRED_FREEP(bp) (*(void**)(bp))             // bp의 predecessor address
#define SUCC_FREEP(bp) (*(void**)(bp + WSIZE))     // bp의 successor address

// static variable
// Doubly Linked List의 시작점을 가르키고 있는 포인터
static char* free_listp;

// static functions
static void* extend_heap(size_t);       // 새 가용 블록으로 heap 확장하는 함수
static void* coalesce(void*);           // 인접 가용 블록들과 합체하는 함수
static void* find_fit(size_t);          // mm_malloc 함수에서 size와 boolean alloc을 확인하는 helper function, explicit allocator에서는 linked list를 탐색함
static void place(void*, size_t);       // mm_malloc 함수에서 block을 할당을 해주는 helper function
static void remove_block(void*);        // linked list에서 블록을 제거하는 함수
static void push_block(void*);          // linked list맨 앞에 삽입해 주는 함수


/* memlib.c
 * void *mem_sbrk(int incr); 함수는 커널의 brk 포인터에 incr을 더해서 힙을 늘리거나 줄인다. 
 * 실패시 [if ((incr < 0)|| (mem_brk + incr > mem_max_addr)] return -1 하고 성공시 return old_ptr값
 */

/* 
 * mm_init - initialize the malloc package
 */
int mm_init(void)
{
    if ((free_listp = mem_sbrk(6*WSIZE)) == (void*)-1)
        return -1;
    PUT(free_listp, 0);                             // alignment padding
    PUT(free_listp + 1*WSIZE, PACK(2*DSIZE, 1));    // prologue header, 32bit에서 포인터는 4byte, 2*DSIZE = 2* pointer + header_size + footer_size
    PUT(free_listp + 2*WSIZE, (int)NULL);           // predecessor pointer
    PUT(free_listp + 3*WSIZE, (int)NULL);           // successor pointer
    PUT(free_listp + 4*WSIZE, PACK(2*DSIZE, 1));    // prologue footer
    PUT(free_listp + 5*WSIZE, PACK(0, 1));          // epilogue header
    free_listp += 2*WSIZE;                          // header에 free_listp 포인터 위치시켜놓음

    // Extend the empty heap with a free block of CHUNKSIZE bytes (초기 가용 블록 생성)
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

// 새 가용 블록으로 heap 확장하는 함수
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

// 인접 가용 블록들과 합체하는 함수
static void* coalesce(void * bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  // 앞의 block의 footer을 확인
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));  // 뒤의 block의 header를 확인 
    size_t size = GET_SIZE(HDRP(bp));
    
    if (prev_alloc && !next_alloc){             // 다음 block만 free면
        remove_block(NEXT_BLKP(bp));            // linked list에서 next_blkp 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  // next block의 header에서 size 받아와서 더해줌
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));           // FTRP는 GET_SIZE(HDRP(bp))를 이용하기 때문에 FTRP(bp)가 next block의 footer을 가르킬거임
    }

    else if (!prev_alloc && next_alloc){           // 전 block만 free면
        remove_block(PREV_BLKP(bp));               // linked list에서 prev_blkp 제거
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));     // previous block의 footer에서 size 받아와서 더해줌
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);                        // bp를 prev_blkp 포인트 하게 해줌
    }

    else if (!prev_alloc && !next_alloc){       // prev & next 둘다 free 면
        remove_block(PREV_BLKP(bp));            // linked list에서 prev_blkp, next_blkp 둘다 제거
        remove_block(NEXT_BLKP(bp));             
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);                      // bp를 prev_blkp 포인트 하게 해줌
    }

    // coalesce 돤 block linked_list앞에 삽입
    push_block(bp);  
    // free_listp = bp; 이건 push block 함수 안에 넣어주자
    return bp;
}

// linked list에서 블록을 제거하는 함수
// doubly linked list의 delete 함수랑 비슷
static void remove_block(void* bp){
    // 맨 앞 block일때
    if (PRED_FREEP(bp) == NULL){
        bp = SUCC_FREEP(bp);
        PRED_FREEP(bp) = NULL;
        //맨 앞 pointer update
        free_listp = bp;
    }
    // 맨 앞 block이 아닐때
    else{
        SUCC_FREEP(PRED_FREEP(bp)) = SUCC_FREEP(bp);
        PRED_FREEP(SUCC_FREEP(bp)) = PRED_FREEP(bp);
    }
}

// linked list맨 앞에 삽입해 주는 함수
static void push_block(void* bp){
    SUCC_FREEP(bp) = free_listp;
    PRED_FREEP(free_listp) = bp;
    PRED_FREEP(bp) = NULL;
    free_listp = bp;
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
        // 8의 배수를 맞춰주기 위한 연산
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/ DSIZE);
    
    // search the free list for a fit
    if ((bp = find_fit(asize)) != NULL){
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
// first fit으로 linked list의 처음부터 검색
static void* find_fit(size_t asize){
    void* bp;
    for (bp = free_listp; bp != NULL; bp = SUCC_FREEP(bp)){
        // 만약 size도 맞고 allocation도 안되있으면
        if (GET_SIZE(HDRP(bp)) >= asize)
            return bp;
    }
    return NULL;
}


// mm_malloc 함수에서 block을 할당을 해주는 helper function
static void place(void* bp, size_t asize){

    size_t csize = GET_SIZE(HDRP(bp));
    remove_block(bp);

    // 만약 사이즈가 커서 split을 할 정도라면
    if (csize >= asize + 2*DSIZE){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        // split된 남은 size의 블록 다시 linked list에 삽입
        push_block(bp);
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
    // coalesce function takes care of linked list deletion and insertion
    coalesce(bp);
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * realloc은 이미 할당한 블록의 크기를 바꿀 때 사용
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    if ((newptr = mm_malloc(size)) == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)               // 인자로 주어진 사이즈가 기존 블록의 사이즈보다 작으면 인자로 주어진 사이즈만큼의 데이터만 잘라서 옮긴다.
      copySize = size;
    memcpy(newptr, oldptr, copySize);  // memcpy는 블록 내 데이터를 옮기는 기본 제공 함수
    mm_free(oldptr);
    return newptr;
}




