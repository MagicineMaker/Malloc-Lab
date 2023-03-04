/*
 * mm.c
 *
 * ZhangAn 2100012975
 *
 * This memory allocator is based on segregated free lists.
 *
 * The smallest block class on the free list is 16 bytes in size,
 * with a header, a footer and the pointer to its successor.
 *
 * There exist free blocks of 8 bytes, owning a header and a footer each,
 * but such blocks can't be found on the free list and are exclusively taken into account when coalescing.
 *
 * Every block has a header.
 * However, only a free block has a footer.
 * Whether the preceding block is allocated is recorded in the second least bit of the header.
 * 
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
#define DEBUG
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
#define NEO_ALIGN(p) (p<5)?12:(ALIGN(p-4)+4)

/* Basic constants and macros */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE 2112
#define CLASSES 26
#define BIAS 2
#define MAX_LEVEL 26
#define MIN_BLOCK_SIZE 16
#define FIRST_BLOCK_SIZE 1504

#define MAX(x,y) ((x>y) ? (x) : (y))
#define MIN(x,y) ((x<y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_PREV_ALLOC(p) (GET(p) & 0x2)

/* Given block pointer bp, compte address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block pointer bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Heap bottom */
static char * heap_listp;

/* Free list */
static char * free_list;

int first=0;

/* Static helper functions */
static char* find_fit(size_t);
static void set_block(char*,size_t,int);
static unsigned int get_class(size_t);
static void remove_from_free_list(char*);
static void add_to_free_list(char*);
static void split_block(char*,size_t);
static char* coalesce(char*);
static char* extend_heap(size_t);
static void set_prev_alloc(char*,int);

/* Find a block that fits size */
static char* find_fit(size_t size){
	for(unsigned int j=get_class(size); j<CLASSES; ++j){
		char* bp = *((char**)(free_list+j*DSIZE));
		while(bp){
			if(GET_SIZE(HDRP(bp))>=size){
				return bp;
			}
			bp = *((char**)bp);
		}
	}
	return NULL;
}

/* Set the header and footer and maintain the prev_alloc bit */
static void set_block(char * bp, size_t size, int alloc){
	unsigned int prev_alloc=(GET(HDRP(bp))&0x2);
	PUT(HDRP(bp), PACK(size, alloc));
	if(!alloc) PUT(FTRP(bp), PACK(size, alloc));
	set_prev_alloc(bp,prev_alloc);
}

/* Which block class to search from? */
static unsigned int get_class(size_t size){
	unsigned int i=BIAS;
	while((((size_t)1)<<(i+3))<size&&i<MAX_LEVEL) ++i;
	i -= BIAS;
	return i;
}

/* Remove the block located at bp from the free list */
static void remove_from_free_list(char * bp){
	/* Remove the block from the class list */
	unsigned int p=get_class(GET_SIZE(HDRP(bp)));
	char* ptr=free_list+DSIZE*p;
	char* tmp;
	while((tmp=*((char**)ptr))!=bp&&tmp) ptr=tmp;

	/* Assert that the entry is in the free list */
	if(!tmp){
		printf("Cannot remove a block that is not here on the free list!\n");
		return;
	}

	*((char**)ptr)=*((char**)bp);
}

/* Add a new free block located at bp to the free list */
static void add_to_free_list(char * bp){
	/* Assert that the entry is a free block */
	if(GET_ALLOC(HDRP(bp))!=0){
		printf("Cannot add an allocated block to the free list!\n");
		return;
	}

	/* Add the block to the class list */
	unsigned int p=get_class(GET_SIZE(HDRP(bp)));
	char * ptr=free_list+p*DSIZE;
	*((char**)bp) = *((char**)ptr);
	*((char**)ptr) = bp;
}

/* Split apart a free block and set the leading block allocated
 * The remaining block is set to a free block */
static void split_block(char * bp, size_t size){
	unsigned int old_size=GET_SIZE(HDRP(bp));

	if(GET_ALLOC(HDRP(bp))==0) remove_from_free_list(bp);

	size_t new_size = size, remaining_size = old_size-size;

	set_block(bp,new_size,1);

	if(remaining_size==0) set_prev_alloc(NEXT_BLKP(bp),2);
	else{
		char *nbp=NEXT_BLKP(bp);
		set_block(nbp,remaining_size,0);
		set_prev_alloc(nbp,2);
		nbp=coalesce(nbp);
		set_prev_alloc(NEXT_BLKP(nbp),0);
		if(GET_SIZE(HDRP(nbp))>=MIN_BLOCK_SIZE) add_to_free_list(nbp);
	}
}

/* Coalesce free blocks */
static char* coalesce(char* bp){
	char *nbp=NEXT_BLKP(bp);

	/* The next block is free */
	if(GET_ALLOC(HDRP(nbp))==0){
		if(GET_SIZE(HDRP(nbp))>=MIN_BLOCK_SIZE) remove_from_free_list(nbp);
		size_t new_size=GET_SIZE(HDRP(bp))+GET_SIZE(HDRP(nbp));
		set_block(bp,new_size,0);
	}

	/* The preceding block is free */
	if(GET_PREV_ALLOC(HDRP(bp))==0){
		char *pbp=PREV_BLKP(bp);
		if(GET_SIZE(HDRP(pbp))>=MIN_BLOCK_SIZE) remove_from_free_list(pbp);
		size_t new_size=GET_SIZE(HDRP(pbp))+GET_SIZE(HDRP(bp));
		set_block(pbp,new_size,0);
		bp=pbp;
	}

	/* Coalesced blocks are surrounded by allocated blocks */
	set_prev_alloc(bp,2);
	set_prev_alloc(NEXT_BLKP(bp),0);

	return bp;
}

/* Apply for extra heap space */
static char* extend_heap(size_t e_size){
	char *bp, *lbp=((char*)mem_heap_hi())+1-WSIZE;
	unsigned int palloc=GET_PREV_ALLOC(lbp);
	size_t new_size;
	e_size=ALIGN(e_size);

	if(e_size>=CHUNKSIZE){
		if((long)(bp=mem_sbrk(e_size))==-1) return NULL;
		else new_size=e_size;
	}
	else{
		if((long)(bp=mem_sbrk(CHUNKSIZE))==-1){
			if((long)(bp=mem_sbrk(e_size))==-1) return NULL;
			else new_size=e_size;
		}
		else new_size=CHUNKSIZE;
	}

	/* Take the newly applied block as a free block */
	set_block(bp,new_size,0);
	set_prev_alloc(bp,palloc);

	/* New epilogue */
	PUT(HDRP(NEXT_BLKP(bp)), 1);

	/* Coalesce if possible */
	bp=coalesce(bp);

	if(GET_SIZE(HDRP(bp))>=MIN_BLOCK_SIZE) add_to_free_list(bp);
	return bp;
}

/* Set the prev_alloc bit to alloc (0 or 2) */
static void set_prev_alloc(char* bp, int alloc){
	unsigned int *header=(unsigned int*)(HDRP(bp));
	(*header) &= 0xfffffffd;
	(*header) |= alloc;

	/* Only a free block has a footer */
	if(GET_ALLOC(HDRP(bp))==0){
		unsigned int * footer=(unsigned int*)(FTRP(bp));
		(*footer) &= 0xfffffffd;
		(*footer) |= alloc;
	}
}

/* Exhibit the current free list */
static void print_list(void){
	for(int i=0;i<CLASSES;++i){
		char *bp=*((char**)(free_list+i*DSIZE));
		int p=1;
		while(bp){
			if(p) printf("Class %d:\n",i);
			p=0;
			if(GET_ALLOC(HDRP(bp))) printf("Allocated ");
			else printf("Free ");
			bp=*((char**)bp);
		}
	}
}

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
	if((long long)(free_list = mem_sbrk(CLASSES*DSIZE))==-1) return -1;

	for(int i=0;i<CLASSES;++i){
		PUT((free_list+DSIZE*i), 0);
		PUT((free_list+DSIZE*i+WSIZE), 0);
	}

	if((long long)(heap_listp = mem_sbrk(2*DSIZE+FIRST_BLOCK_SIZE))==-1) return -1;
	heap_listp += DSIZE;

	/* Prologue block */
	PUT((heap_listp-WSIZE), 9);
	PUT((heap_listp), 9);

	/* First free block */
	set_block(heap_listp+DSIZE,FIRST_BLOCK_SIZE,0);
	set_prev_alloc(heap_listp+DSIZE,2);
	add_to_free_list(heap_listp+DSIZE);

	/* Epilogue block hdr */
	PUT(heap_listp+WSIZE+FIRST_BLOCK_SIZE, 1);

	return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) {
	//mm_checkheap(__LINE__);

	if(size==0) return NULL;

	/* Size -> Required block size */
	size_t block_size = (NEO_ALIGN(size))+WSIZE;
	char* bp;

	/* If there exists a fit... */
	if((bp=find_fit(block_size))!=NULL){
		split_block(bp,block_size);
		return bp;
	}

	/* Else... apply for extra heap space */
	if((bp=extend_heap(block_size))!=NULL){
		split_block(bp,block_size);
		return bp;
	}

    return NULL;
}

/*
 * free
 */
void free (void *ptr) {
	//mm_checkheap(__LINE__);

	/* No need to free */
    if(!ptr) return;
	if(GET_ALLOC(HDRP(ptr))==0) return;

	set_block(ptr,GET_SIZE(HDRP(ptr)),0);
	ptr=coalesce(ptr);
	add_to_free_list(ptr);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
	//mm_checkheap(__LINE__);

	if(oldptr==NULL) return malloc(size);
	if(size==0){
		free(oldptr);
		return NULL;
	}

	size_t block_size=(NEO_ALIGN(size))+WSIZE, old_size=GET_SIZE(HDRP(oldptr));

	char *next_block=NEXT_BLKP(oldptr)/*, *prev_block=PREV_BLKP(oldptr)*/;
	size_t next_size=GET_SIZE(HDRP(next_block))/*, prev_size=GET_SIZE(HDRP(prev_block))*/,
	write_size=MIN(old_size, block_size);
	int next_alloc=GET_ALLOC(HDRP(next_block)), prev_alloc=GET_PREV_ALLOC(HDRP(oldptr));

	/* Just extend the current block? */
	if(prev_alloc==0){
		char *prev_block=PREV_BLKP(oldptr);
		size_t prev_size=GET_SIZE(HDRP(prev_block));
		if(old_size+prev_size>=block_size){
			if(prev_size>=MIN_BLOCK_SIZE) remove_from_free_list(prev_block);
			memcpy(prev_block,oldptr,write_size-WSIZE);
			set_block(prev_block,old_size+prev_size,1);
			split_block(prev_block,block_size);
			return prev_block;
		}
		else if(next_alloc==0&&old_size+prev_size+next_size>=block_size){
			if(prev_size>=MIN_BLOCK_SIZE) remove_from_free_list(prev_block);
			if(next_size>=MIN_BLOCK_SIZE) remove_from_free_list(next_block);
			memcpy(prev_block,oldptr,write_size-WSIZE);
			set_block(prev_block,old_size+prev_size+next_size,1);
			split_block(prev_block,block_size);
			return prev_block;
		}
	}
	if(old_size>=block_size){
		split_block(oldptr,block_size);
		return oldptr;
	}
	else if(next_alloc==0&&old_size+next_size>=block_size){
		if(next_size>=MIN_BLOCK_SIZE) remove_from_free_list(next_block);
		set_block(oldptr,old_size+next_size,1);
		split_block(oldptr,block_size);
		return oldptr;
	}

	/* Remember the first DWORD and the last WORD, which will be lost in the call of free */
	unsigned long tmp=*((unsigned long*)oldptr);
	unsigned int tmp1=*((unsigned int*)(FTRP(oldptr)));
	free(oldptr);
	char* newptr;
	if((newptr=malloc(size))!=NULL){
		*((unsigned long*)newptr)=tmp;
		*((unsigned int*)(newptr+old_size-DSIZE))=tmp1;
		memcpy(((char*)newptr)+DSIZE,((char*)oldptr)+DSIZE,old_size-2*DSIZE);
		return newptr;
	}

    return NULL;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
	if(nmemb==0||size==0) return NULL;
	void* bp=malloc(nmemb*size);
	memset(bp,0,nmemb*size);
    return bp;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap
 */
void mm_checkheap(int lineno) {
	char *a=NEXT_BLKP(heap_listp),*b=heap_listp;

	/* Check for invalid blocks in the heap */
	while(GET_SIZE(HDRP(a))!=0){
		if(GET_ALLOC(HDRP(b))==0&&GET_ALLOC(HDRP(a))==0){
			printf("The two free block are not coalesced!\n%lx\n%lx\n",(size_t)b,(size_t)a);
			exit(0);
		}
		if(GET_ALLOC(HDRP(b))&&GET_PREV_ALLOC(HDRP(a))==0){
			printf("Block %lx is allocated but block %lx has 0 prev_alloc bit!\n",(size_t)b,(size_t)a);
			exit(0);
		}
		if(GET_ALLOC(HDRP(b))==0&&GET_PREV_ALLOC(HDRP(a))){
			printf("Block %lx is free but block %lx has 1 prev_alloc bit!\n",(size_t)b,(size_t)a);
			exit(0);
		}
		if(GET_ALLOC(HDRP(a))==0&&GET(HDRP(a))!=GET(FTRP(a))){
			printf("The free block at %lx has different header and footer!\nHeader: %o\nFooter: %o",
			(size_t)a,GET(HDRP(a)),GET(FTRP(a)));
			exit(0);
		}
		b=a;
		a=NEXT_BLKP(a);
	}

	/* Check for invalid blocks in the free list */
	for(int i=0;i<CLASSES;++i){
		char *ptr=*((char**)(free_list+i*DSIZE));
		while(ptr){
			if(GET_ALLOC(HDRP(ptr))){
				printf("Allocated block %lx found on the free list!\n",(size_t)ptr);
				exit(0);
			}
			ptr=*((char**)ptr);
		}
	}
}
