/*
 * mm.c
 *
 * Name: [Yang Xu, Zhemin Wang]
 *
 We make a segmented list for storing dynamically allocated data. The seglist word
 like this: all of the aligned size smaller than 256 is precessed into 16 different class 
 bins(0-15), from 256+16 to 32768 bytes are exponentially assigned to class bins(16-22), 
 for all the aligned size greater than 32768, we assign them to class bin 23. The mechanism 
 inside in seglist is explicit free lists, whose head in stored in the starting 23 words 
 of the heap(prologue) and tail is the epilogue. 
 
 the epilogue is consisted of class bins that contains the addr of first free block of the class:
 |class_0_ptr|class_1_ptr|class_2_ptr|class_3_ptr|class_4_ptr|class_5_ptr|...
 
 We use prev and next pointers to connect 
 all the free blocks together: 
 (prologue)->|header|prev|next|PAYLOAD|footer|->some free block->(epilogue), 
 if the prev is prologue, we store 0 in prev;
 if the next is epilogue, we store 0 in next;

 for allocated blocks, we only use headers to indicate its length and allocated status of curr and left:
 |header|PAYLOAD|

 any new allocated block will be removed from class free list
 any new freed block will be coalesced with left and right block and inserted into class free list

 Note that we used a different system that aligns 8 bytes more than normal 
 but dropped footers for allocated blocks
 *
 */
#include <math.h>
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
// #define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */

/* What is the correct alignment and wordsize? */
#define ALIGNMENT 16
#define WORDSIZE 8

// whether the heap system started
static bool initialized = false;

// points to the lowest address of the heap
uint8_t *heap_start;

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

static size_t align_new(size_t x)
{
    return ALIGNMENT * ((x + WORDSIZE + ALIGNMENT - 1) / ALIGNMENT) - WORDSIZE;
}

// get the length from a header/footer
uint64_t getLength(uint8_t* ptr){
    uint64_t space;
    mem_memcpy(&space, ptr, WORDSIZE);

    return (space / WORDSIZE) * WORDSIZE;
}

bool getLeftAllocated(uint8_t* ptr){
    uint64_t space;
    mem_memcpy(&space, ptr, WORDSIZE);

    return (space % 4 == 2) || (space % 4 == 3);
}

// construct() new version
void construct_new(uint8_t *ptr, uint64_t length, bool currAllocated, bool leftAllocated){
    uint64_t space = length;
    if(currAllocated)
        space |= 0x1;
    if(leftAllocated)
        space |= 0x2;
    mem_memcpy(ptr, &space, WORDSIZE);
}

// deconstruct() new version
void deconstruct_new(uint8_t *ptr, uint64_t* length, bool* currAllocated, bool* leftAllocated){
    uint64_t space;
    mem_memcpy(&space, ptr, WORDSIZE);

    *length = (space / WORDSIZE) * WORDSIZE;
    *currAllocated = (space % 2 == 1);
    *leftAllocated = (space % 4 == 2) || (space % 4 == 3);
}

void setLeftAllocated(uint8_t* ptr, bool leftAllocated){
    uint64_t length;
    bool currAllocated;
    bool d; // dummy variable
    deconstruct_new(ptr, &length, &currAllocated, &d);
    construct_new(ptr, length, currAllocated, leftAllocated);
}

// fit the blocks into classes according to required bytes
uint64_t calculateClass_new(uint64_t requiredBytes){
    uint64_t aligned_to_16 = requiredBytes + WORDSIZE;
    if(aligned_to_16<=256)
       return (uint64_t)(aligned_to_16/ALIGNMENT) - 1;
    else if(aligned_to_16<=32768)
       return (uint64_t)ceil(log(aligned_to_16)/log(2)) + 7;
    else
       return 23;
}

/*
 * Initialize: returns false on error, true on success.
 */
bool mm_init(void)    
{
    if(mem_sbrk(26 * WORDSIZE)==NULL){
        return false;
    }

    // initialize heap_start
    heap_start = (uint8_t *)mem_heap_lo();
    
    // 12 seglists and prologue and epilogue, 14 in total
    mem_memset(heap_start, 0, 26 * WORDSIZE);

    /* last byte of epilogue and prologue: 00000011 or 3
    (prevAllocated and currAllocated indicated in the last two bits) */

    // set prologue
    construct_new(heap_start + 24 * WORDSIZE, 0, true, true);
    // set epilogue
    construct_new(heap_start + 25 * WORDSIZE, 0, true, true);

    initialized = true;
    return true;
}

// some helper methods
void insertIntoFreeList(uint8_t* class_addr, uint8_t* curr_addr){

    uint8_t* first_addr;
    mem_memcpy(&first_addr, class_addr, WORDSIZE);

    // the list is not empty
    if(first_addr != 0x0){
        mem_memcpy(first_addr + WORDSIZE, &curr_addr, WORDSIZE); // first.prev
        mem_memcpy(class_addr, &curr_addr, WORDSIZE); // class.next
        mem_memset(curr_addr + WORDSIZE, 0x0, WORDSIZE); // curr.prev
        mem_memcpy(curr_addr + 2 * WORDSIZE, &first_addr, WORDSIZE);// curr.next
    }else{
        mem_memcpy(class_addr, &curr_addr, WORDSIZE); // class.next
        mem_memset(curr_addr + WORDSIZE, 0x0, WORDSIZE); // curr.prev
        mem_memset(curr_addr + 2 * WORDSIZE, 0x0, WORDSIZE);// curr.next
    }

}

void removeFromFreeList(uint8_t* start_addr, uint64_t length){

    uint64_t* prev;
    uint64_t* next;
    uint8_t* class_addr = heap_start + calculateClass_new(length) * WORDSIZE;

    // get prev and next pointers
    mem_memcpy(&prev, start_addr + WORDSIZE, WORDSIZE);
    mem_memcpy(&next, start_addr + 2 * WORDSIZE, WORDSIZE);
    
    // () -> curr -> [some block]
    if(prev == 0x0 && next != 0x0){
        mem_memcpy(class_addr, &next, WORDSIZE); // class.next
        mem_memset((uint8_t*)next + WORDSIZE, 0x0, WORDSIZE); // next.prev
    // [some block] -> curr -> [some block]
    }else if(prev != 0x0 && next != 0x0){
        mem_memcpy((uint8_t*)prev + 2 * WORDSIZE, &next, WORDSIZE); // prev.next
        mem_memcpy((uint8_t*)next + WORDSIZE, &prev, WORDSIZE); // next.prev
    // () -> curr -> ()
    }else if(prev == 0x0 && next == 0x0){
        mem_memset(class_addr, 0x0, WORDSIZE); // class.next
    // [some block] -> curr -> ()
    }else{
        mem_memset((uint8_t*)prev + 2 * WORDSIZE, 0x0, WORDSIZE); // prev.next
    }
}

// request more heap space from mem_sbrk()
void* allocateExtra(uint64_t requiredBytes){

    // new and old epilogue addresses
    uint8_t* old_epi_addr = (uint8_t*)(mem_heap_hi() - 7);
    uint8_t* new_epi_addr = old_epi_addr + (requiredBytes + WORDSIZE);

    bool leftAllocated; 

    // get extra space in the heap and shift the epilogue
    if(mem_sbrk(requiredBytes + WORDSIZE) == (void *)-1){
        return NULL;
    }
    mem_memcpy(new_epi_addr, old_epi_addr, WORDSIZE);

    // get leftAllocated of epilogue
    leftAllocated = getLeftAllocated(old_epi_addr);   
    // build header of the extra allocated block
    construct_new(old_epi_addr, requiredBytes, true, leftAllocated);
    // set leftAllocated of epilogue to true
    setLeftAllocated(new_epi_addr, true);

    return (void *)(old_epi_addr + WORDSIZE);
}


// create a implicit block at the specified location
void* allocateWithinHeap(uint8_t* start_addr, uint64_t requiredBytes, uint64_t length, uint64_t class){

    bool leftAllocated = getLeftAllocated(start_addr);

    removeFromFreeList(start_addr, length);
    
    // construct header for the allocated block
    construct_new(start_addr, requiredBytes, true, leftAllocated);
    
    // (possible) allocate with splitting
    if(requiredBytes < length){
        // construct header and footer for the block to the right after splitting and try to free it
        construct_new(start_addr + requiredBytes + WORDSIZE, length - requiredBytes - WORDSIZE, false, true);
        construct_new(start_addr + length, length - requiredBytes - WORDSIZE, false, true);

        free(start_addr + requiredBytes + 2 * WORDSIZE);
    }else{
        // set the leftAllocated bit in header of right block to be true
        setLeftAllocated(start_addr + length + WORDSIZE, true);
    }

    return (void *)(start_addr + WORDSIZE);
}


/*
 * malloc
 */
void* malloc(size_t size)
{
    if(!initialized||size<=0)
        return NULL;

    uint64_t requiredBytes = (uint64_t)align_new(size);
    // curr_addrent class
    uint64_t class = calculateClass_new(requiredBytes);

    // iterative pointer
    uint8_t* curr_addr;

    // whether already jumped class
    bool jumped = false;

    // info of the curr_addr block
    uint64_t length;

    // best fit info
    uint64_t bestLength = 0;
    uint8_t* best_addr = 0;

    // loop of class traversal
    while(class < 24){
        
        bestLength = 0;
        best_addr = 0x0;

        mem_memcpy(&curr_addr, heap_start + class * WORDSIZE, WORDSIZE);

        while(curr_addr != 0){

            length = getLength(curr_addr);

            if(class < 16){
                return allocateWithinHeap(curr_addr, requiredBytes, length, class);    
            }else{
                // cannot allocate at curr_addr, if not enough space
                if(requiredBytes == length){
                    return allocateWithinHeap(curr_addr, requiredBytes, length, class);
                }else if(requiredBytes < length){
                    if(bestLength == 0){
                        bestLength = length;
                        best_addr = curr_addr;
                    }else if(length < bestLength){
                        bestLength = length;
                        best_addr = curr_addr;
                    }
                }
                // curr = curr.next
                mem_memcpy(&curr_addr, curr_addr + 2 * WORDSIZE, WORDSIZE); // curr = curr.next
            }
        }

        // check whether a adequate block is found
        if(bestLength != 0)
            return allocateWithinHeap(best_addr, requiredBytes, bestLength, class);
            
        // go to next loop when class pointer is empty(pointing to epilogue)
        if(class < 16 && !jumped){
            class += 2;
            jumped = true;      
        }else{
            class += 1;
        }
    }

    // failed to find an length-adequate block, grow heap
    return allocateExtra(requiredBytes);
}

/*
 * free
 */
void free(void* ptr)
{ 

    if(ptr == NULL)
        return;

    uint8_t* curr_addr = (uint8_t *)ptr; // currently freeing payload address
    uint8_t* class_addr; // prologue class head address
    
    // info for current, right and left block
    uint64_t curr_length;
    bool a; // =curr_allocated
    bool left_allocated;

    uint64_t right_length;
    bool right_allocated;
    bool b; // =curr_allocated

    uint64_t left_length = 0;
    bool c; // =left_allocated
    bool left_left_allocated = false;

    uint64_t total_length; // total length of coalesced block

    // analyze current and right block and analyze left block conditionally
    deconstruct_new(curr_addr - WORDSIZE, &curr_length, &a, &left_allocated);
    deconstruct_new(curr_addr + curr_length, &right_length, &right_allocated, &b);


    if(!left_allocated){
        deconstruct_new(curr_addr - 2 * WORDSIZE, &left_length, &c, &left_left_allocated);
    }

    // allocated | curr | allocated
    if(left_allocated && right_allocated){ // just construct a free block here
        // 1. calculate total length
        total_length = curr_length;

        // 2. get the class and curr block addresses
        class_addr = heap_start + calculateClass_new(total_length) * WORDSIZE;
        curr_addr -= WORDSIZE;

        // 3. remove the previous and next block from their respective free list

        // 4. construct header for the coalesced block
        construct_new(curr_addr, total_length, false, true);
        mem_memcpy(curr_addr + total_length, curr_addr, WORDSIZE);

    // allocated | curr | free
    }else if(left_allocated && !right_allocated){
        // 1. calculate total length
        total_length = curr_length + WORDSIZE + right_length;

        // 2. get the class and curr block addresses
        class_addr = heap_start + calculateClass_new(total_length) * WORDSIZE;
        curr_addr -= WORDSIZE;

        // 3. remove the previous and next block from their respective free list
        if(right_length > WORDSIZE)
            removeFromFreeList(curr_addr + curr_length + WORDSIZE, right_length);
        
        // 4. construct header and footer for the coalesced block
        construct_new(curr_addr, total_length, false, true);
        mem_memcpy(curr_addr + total_length, curr_addr, WORDSIZE);

    // free | curr | allocated
    }else if(!left_allocated && right_allocated){
        // 1. calculate total length
        total_length = left_length + WORDSIZE + curr_length;

        // 2. get the class and curr block addresses
        class_addr = heap_start + calculateClass_new(total_length) * WORDSIZE;
        curr_addr -= (2 * WORDSIZE + left_length);

        // 3. remove the previous and next block from their respective free list
        if(left_length > WORDSIZE)
            removeFromFreeList(curr_addr, left_length);
        
        // 4. construct header and footer for the coalesced block
        construct_new(curr_addr, total_length, false, left_left_allocated);
        mem_memcpy(curr_addr + total_length, curr_addr, WORDSIZE);
    // free | curr | free
    }else{
        // 1. calculate total length
        total_length = left_length + curr_length + right_length + 2 * WORDSIZE;

        // 2. get the class and curr block addresses
        class_addr = heap_start + calculateClass_new(total_length) * WORDSIZE;
        curr_addr -= (2 * WORDSIZE + left_length);

        // 3. remove the previous and next block from their respective free list
        if(left_length > WORDSIZE)
            removeFromFreeList(curr_addr, left_length);
        if(right_length > WORDSIZE)
            removeFromFreeList(curr_addr + left_length + curr_length + 2 * WORDSIZE, right_length);
        
        // 4. construct header and footer for the coalesced block
        construct_new(curr_addr, total_length, false, left_left_allocated);
        mem_memcpy(curr_addr + total_length, curr_addr, WORDSIZE);

    }
    // 5. (shared)set leftAllocated bit of next block to 0
        setLeftAllocated(curr_addr + WORDSIZE + total_length, false);

    // 6. (shared)insert the claoesced block at the head of the free list
    if(total_length > WORDSIZE)
        insertIntoFreeList(class_addr, curr_addr);
} 

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{
    // check special conditions
    if(oldptr == NULL)
        return malloc(size);
    
    if(size == 0){
        free(oldptr);
        return NULL;
    }

    uint8_t *old_payload_addr = (uint8_t *)oldptr;
    // get original payload length and requested payload length
    uint64_t original_length;
    bool a; // curr_allocated
    bool left_allocated;
    deconstruct_new(old_payload_addr - WORDSIZE, &original_length, &a, &left_allocated);

    uint64_t requested_length = (uint64_t)align_new(size);

    if(requested_length < original_length){ // then split the block

        // shrink the original block
        construct_new(old_payload_addr - WORDSIZE, requested_length, true, left_allocated);

        // build a block in the back and try to coalesce it with the one in the back
        construct_new(old_payload_addr + requested_length, original_length - requested_length - WORDSIZE, false, true);
        construct_new(old_payload_addr + original_length - WORDSIZE, original_length - requested_length - WORDSIZE, false, true);
        free((void *)(old_payload_addr + requested_length + WORDSIZE));

        // set leftAllocated bit of next block
        setLeftAllocated(old_payload_addr + original_length, false);

        return oldptr;

    }else if(requested_length > original_length){

        uint8_t* newptr = malloc(requested_length);
        if(newptr == NULL)
            return NULL;

        mem_memcpy(newptr, oldptr, original_length);
        free(oldptr);
        return newptr;

    }else{ // original and requested length are the same
        return oldptr;
    }
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno)
{
//#ifdef DEBUG
    
//#endif /* DEBUG */

    // scan from start to the end of heap to check
    // whether all the payload are aligned to 16
    uint8_t* curr_addr = heap_start + 25 * WORDSIZE;
    //check until it reached the epilogue
    while(curr_addr < (uint8_t *)(mem_heap_hi() - 7)){
        if(!aligned(curr_addr + WORDSIZE))
            return false;
        if(!in_heap(curr_addr))
            return false;
        // deconstruct process
        uint64_t length;
        bool currAllocated;
        bool leftAllocated;
        deconstruct_new(curr_addr, &length, &currAllocated, &leftAllocated);
        // next iteration
        curr_addr += (length + WORDSIZE);
    }
    return true;
}
