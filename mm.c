/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-513: Introduction to Computer Systems
 *
 * In this malloc lab, I've used several tricks to optimize it. However, I use
 * the segregated list in a big picture.
 *
 * First Trick:
 * I'vd distributed 15 roots in two parts. The first past uses 8 roots,
 * and the second part uses 7 root. The difference of the size / size range of
 * consecutive roots is 16. Their sizes are 16, 32, 48, 64, 80, 96, 112, 128. In
 * the second part, the range of each root as follow: (128, 256], (256, 512],
 * (512, 1024], (1024, 2048], (2048, 4096], (4096, 8192], (8192, postive
 * infinity)
 *
 * Second Trick:
 * When the size is euqal to minimum size, then only use single linked list.
 * Other sizes, all use doubly, circular linked list.
 *
 * Third Trick:
 * I've designed three finding algorithms, there are first_fit, best_fit, and
 * better_fit. But evidence proved that better_fit is some kind of compromise of
 * first_fit and best_fit. Better-fit algorithm can find better blocks, which is
 * better than first_fit, and it also is much faster than best_fit. So it has
 * the advantages of first_fit and best_fit.
 *
 * Fourth Trick:
 * I've designed two insertion policies, which are FIFO and LIFO.
 * I decided to use LIFO in this lab. By taking advantages of circular, doubly
 * linked list, I can easily switch different insertion policies, and experiment
 * proves that LIFO has better perfomance.
 *
 * Attention 1: the function of last three bits as follow:
 *
 * The last bit:
 * indicates the allocation status
 * 1 means allocated, 0 means free
 *
 * The second last bit:
 * indicates the allocation status of previous blocks,
 * 1 means allocated, 0 means free
 *
 * The third last bit:
 * indicates is the size of previous blocks is minimum block size(16 bytes)
 * 1 means it equals to the minimum block size, 0 means it's not equal to the
 * minimum block size
 *
 *
 * Attention 2: The data structures
 * When the size of blocks is equal to 16 bytes, the data structure is a single
 * linked list Other sizes of blocks are all using circular, doubly linked list
 *
 * @author Tao Wang <taowang@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */
/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */

#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/************************************************
 *         Policies are managed here            *
 ************************************************/

/** @brief if LIFO = 1, then use LIFO, else use FIFO */
#define LIFO 1

/** @brief if NEXT_FIT = 1, then use next-fit */
#define NEXT_FIT 0

/**
 * If FIT_TYPE == 0, which indicates first fit
 * If FIT_TYPE == 1, which indicates best fit
 * If FIT_TYPE == 2, which indicates better fit
 */
#define FIT_TYPE 2

/** @brief The search range of better-fit algorithm. */
#define BETTER_RANGE 10

/** @brief The total number of roots */
#define SEG_SIZE 15

/** @brief The number of small roots, which increment by 16 bytes */
#define SMALL_INC 8

/** @brief Basic constants */
typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = dsize;

/** @brief When space is not enough, then extend heap by chunk size */
static const size_t chunksize = (1 << 12);

/** @brief This mask is to get current allocation status */
static const word_t alloc_mask = 0x1;

/** @brief This mask is to get the allocation statu of previous blocks */
static const word_t prev_alloc_mask = 0x2;

/** @brief This mask is to set previous allocation statu as free block */
static const word_t prev_free_mask = ~(word_t)0x2;

/** @brief Use it to identify is the size of previous free blocks 16 bytes */
static const word_t prev_size_mask = 0x4;

/** @brief Set the size of previous block status as minimum block size */
static const word_t negated_prev_size_mask = ~(word_t)0x4;

/** @brief Use this mask to extract the size of blocks */
static const word_t size_mask = ~(word_t)0xF;

typedef struct block block_t;
/** @brief Represents the header and payload of one block in the heap */
struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;

    /** @brief A pointer to the block payload. */
    char payload[0];
};

/* Global variables */
static block_t *root[SEG_SIZE];

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` of a block into a word suitable for
 *        use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc, bool prev_alloc, bool prev_size) {
    word_t word = size;
    if (alloc && prev_alloc) {
        word = word | alloc_mask | prev_alloc_mask;
    } else if (alloc && !prev_alloc) {
        word |= alloc_mask;
    } else if (!alloc && prev_alloc) {
        word |= prev_alloc_mask;
    }

    if (prev_size) {
        word = word | prev_size_mask;
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) >= 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}

/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    bool alloc = get_alloc(block);
    size_t asize = get_size(block);
    if (alloc == true)
        return asize - wsize;
    return asize - dsize;
}

/**
 * @brief Returns the previous allocation status of a current block, based on
 * its header value.
 *
 * @param[in] word
 * @return The allocation status of the block's previous block.
 */
static bool extract_prev_alloc(word_t word) {
    return (bool)((word & prev_alloc_mask) >> 1);
}

/**
 * @brief Returns the size of previous blocks, based on its header value.
 * @param[in] word
 * @return The allocation status of the block's previous block.
 */
static bool extract_prev_size(word_t word) {
    return (bool)((word & prev_size_mask) >> 2);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 */
static void write_epilogue(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == mem_heap_hi() - 7);
    block->header = pack(0, true, false, false);
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] alloc The allocation status of the new block
 * @param[in] Is using write_block function in extend_block
 * @param[in] split_type  0 means not split; 1 means split first write_block in
 * split_block; 2 means split second write_block in split_block
 */
static void write_block(block_t *block, size_t size, bool alloc, bool is_extend,
                        int split_type) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);

    // Get prev allocation status
    bool prev_alloc = extract_prev_alloc(block->header);
    bool prev_size = extract_prev_size(block->header);
    if (block == heap_start || split_type == 2) {
        prev_alloc = true;
    }

    // update current block
    // update header
    block->header = pack(size, alloc, prev_alloc, prev_size);
    // only free blocks, their size is greater than the minimum block size, need
    // write a footer
    if (alloc == false && size > min_block_size) {
        word_t *footerp = header_to_footer(block);
        *footerp = pack(size, alloc, prev_alloc, prev_size);
    }

    // Not update extend_block
    if (is_extend == false && split_type != 1) {
        block_t *next = find_next(block);
        bool next_alloc_status = get_alloc(next);
        size_t next_size = extract_size(next->header);

        // update next block's prev allocation status.
        if (alloc == true) {
            next->header = next->header | prev_alloc_mask;
            if (next_alloc_status == false && next_size > min_block_size) {
                word_t *next_footerp = header_to_footer(next);
                *next_footerp = (*next_footerp) | prev_alloc_mask;
            }
        } else {
            next->header = next->header & prev_free_mask;
            if (next_alloc_status == false && next_size > min_block_size) {
                word_t *next_footerp = header_to_footer(next);
                *next_footerp = (*next_footerp) & prev_free_mask;
            }
        }

        // update next block's prev size status (previous size = 16, then set to
        // 1)
        if (size == min_block_size) {
            next->header = next->header | prev_size_mask;
            if (next_alloc_status == false && next_size > min_block_size) {
                word_t *next_footerp = header_to_footer(next);
                *next_footerp = (*next_footerp) | prev_size_mask;
            }
        } else {
            next->header = next->header & negated_prev_size_mask;
            if (next_alloc_status == false && next_size > min_block_size) {
                word_t *next_footerp = header_to_footer(next);
                *next_footerp = (*next_footerp) & negated_prev_size_mask;
            }
        }
    }
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @param[out] The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);

    if (extract_prev_size(block->header) == true)
        return (block_t *)((word_t *)block - 2);

    word_t *footerp = find_prev_footer(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*footerp) == 0) {
        return NULL;
    }

    return footer_to_header(footerp);
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN MY FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Finds the right root for given block sizes
 * @param[in] The size of a block
 * @param[out] The index of its root
 */
static size_t get_root_index(size_t size) {
    size_t base_size = SMALL_INC * dsize;
    if (size <= base_size) {
        return size / dsize - 1;
    }

    base_size = base_size * 2;
    for (size_t i = 0; i < SEG_SIZE - SMALL_INC - 1; i++) {
        if (size <= base_size)
            return SMALL_INC + i;
        base_size = base_size * 2;
    }

    return SEG_SIZE - 1;
}

/**
 * @brief Finds the next free block in circular, doubly linked list.
 * @param[in] block A block in the heap
 * @return The next block in circular, doubly linked list.
 */
static block_t *get_next_free(block_t *block) {
    word_t *next_free = &(block->header) + 1;
    return (block_t *)(*next_free);
}

/**
 * @brief Finds the previous free block in circular, doubly linked list.
 * @param[in] block A block in the heap
 * @return The previous block in circular, doubly linked list.
 */
static block_t *get_prev_free(block_t *block) {
    word_t *prev_free = &(block->header) + 2;
    return (block_t *)(*prev_free);
}

/**
 * @brief Sets the next block in circular, doubly linked list.
 * @param[in] block A block in the heap
 * @return The next block in circular, doubly linked list.
 */
static void set_next_free(block_t *block, block_t *next_block) {
    word_t *next_free = &(block->header) + 1;
    *next_free = (word_t)next_block;
}

/**
 * @brief Sets the previous free-block pointer in a block.
 * @param[in] A block in the heap
 */
static void set_prev_free(block_t *block, block_t *prev_block) {
    word_t *prev_free = &(block->header) + 2;
    *prev_free = (word_t)prev_block;
}

/**
 * @brief Check if there is only one free block in the list.
 * @param[out] Judgment result.
 */
static bool is_single_block_list(block_t *root) {
    block_t *next_free = get_next_free(root);
    block_t *prev_free = get_prev_free(root);

    return (next_free == root) && (prev_free == root);
}

/**
 * @brief Remove a 16-byte free block in the list.
 * @param[in] A 16-byte block in the heap
 */
static void remove_free_16(block_t *block) {
    // Only one block in the linked list or this block is the first block
    // in the list.
    if (root[0] == block) {
        root[0] = get_next_free(block);
        return;
    }

    block_t *prev = root[0];
    block_t *cur = get_next_free(prev);

    while (cur != block) {
        prev = cur;
        cur = get_next_free(cur);
    }

    block_t *next = get_next_free(cur);
    set_next_free(prev, next);
}

/**
 * @brief Insert a 16-byte free block in the list.
 * @param[in] A 16-byte block in the heap
 */
static void insert_free_16(block_t *block) {
    set_next_free(block, root[0]);
    root[0] = block;
}

/**
 * @brief Remove a free block in the list.
 * @param[in] A block in the heap
 */
static void remove_free(block_t *block) {
    dbg_requires(block != NULL);

    size_t idx = get_root_index(get_size(block));

    if (idx == 0) {
        remove_free_16(block);
        return;
    }

    if (is_single_block_list(root[idx])) {
        root[idx] = NULL;
        return;
    }

    block_t *prev_free = get_prev_free(block);
    block_t *next_free = get_next_free(block);

    // Update previous free block
    set_next_free(prev_free, next_free);

    // Update next free block
    set_prev_free(next_free, prev_free);

    if (root[idx] == block)
        root[idx] = prev_free;
}

/**
 * @brief Substitute a block to next_block from a list.
 * that is, remove cur_block from the list, then add next_block at the same
 * position in the list.
 * @param[in] A block in the heap
 */
static void substitute_free(block_t *block, block_t *next_block) {
    size_t idx = get_root_index(get_size(block));

    if (is_single_block_list(root[idx])) {
        set_prev_free(next_block, next_block);
        set_next_free(next_block, next_block);
        if (root[idx] == block)
            root[idx] = next_block;
        return;
    }

    block_t *prev_free = get_prev_free(block);
    block_t *next_free = get_next_free(block);
    set_prev_free(next_block, prev_free);
    set_next_free(next_block, next_free);
    set_next_free(prev_free, next_block);
    set_prev_free(next_free, next_block);
    if (root[idx] == block)
        root[idx] = next_block;
}

/**
 * @brief Using FIFO insertion policy to insert a free block in the free list.
 * @param[in] A free block.
 */
static void FIFO_insertion(block_t *block, size_t index) {
    if (root[index] == NULL) {
        set_prev_free(block, block);
        set_next_free(block, block);
        root[index] = block;
        return;
    }
    // Set block
    block_t *prev_free = get_prev_free(root[index]);
    set_prev_free(block, prev_free);
    set_next_free(block, root[index]);

    // Update previous free block
    set_next_free(prev_free, block);

    // Update next free block
    set_prev_free(root[index], block);
}

/**
 * @brief Using LIFO insertion policy to insert a free block in the free list.
 * @param[in] A free block.
 */
static void LIFO_insertion(block_t *block, size_t index) {
    dbg_assert(block != NULL);
    if (root[index] == NULL) {
        set_prev_free(block, block);
        set_next_free(block, block);
        root[index] = block;
        return;
    }
    // Set block
    block_t *next_free = get_next_free(root[index]);
    set_prev_free(block, root[index]);
    set_next_free(block, next_free);

    // Update previous free block
    set_next_free(root[index], block);

    // Update next free block
    set_prev_free(next_free, block);
}

/**
 * @brief Integrate 2 insertion policies, choose one insertion policy that is
 * suitale. Including LIFO and FIFO insertion policies. It also decides that
 * update root policies, which are first fit and next fit.
 * @param[in] A free block to be added into the corresponding free list.
 */
static void insert_free_block(block_t *block) {
    size_t idx = get_root_index(get_size(block));

    if (idx == 0) {
        insert_free_16(block);
        return;
    }

    // Use FIFO or LIFO
    dbg_assert(block != NULL);
    if (LIFO == 1)
        LIFO_insertion(block, idx);
    else
        FIFO_insertion(block, idx);

    // Update root's position
    if (NEXT_FIT == 1)
        root[idx] = block;
}

/**
 * @brief Iterate the free list from root, find the first qualifed block.
 * If there is no suitable block, then return NULL.
 * @param[in] The size of free block it requests
 * @param[out] The address of the qualified free block.
 */
static block_t *first_fit(word_t asize, size_t index) {

    for (size_t i = index; i < SEG_SIZE; i++) {
        if (root[i] == NULL)
            continue;

        block_t *block = root[i];
        do {
            if (asize <= get_size(block)) {
                if (NEXT_FIT == 1 && index != 0)
                    root[i] = block;
                return block;
            }
            block = get_next_free(block);
        } while (block != root[i]);
    }

    return NULL;
}

/**
 * @brief Iterate the free list from root, find the best free block.
 * If there is no suitable block, then return NULL.
 * @param[in] The size of free block it requests
 * @param[out] The address of the best free block.
 */
static block_t *best_fit(word_t asize, size_t index) {
    if (index == 0 && root[index] != NULL)
        return first_fit(asize, index);

    for (size_t i = index; i < SEG_SIZE; i++) {
        if (root[i] == NULL)
            continue;

        block_t *block = root[i];
        block_t *best_block = NULL;
        word_t min_diff = UINT64_MAX, cur_size;

        do {
            cur_size = get_size(block);
            if (asize <= cur_size) {
                if (cur_size - asize < min_diff) {
                    min_diff = cur_size - asize;
                    best_block = block;
                }
            }
            block = get_next_free(block);
        } while (block != root[i]);

        if (best_block != NULL) {
            if (NEXT_FIT == 1)
                root[i] = best_block;
            return best_block;
        }
    }
    return NULL;
}

/**
 * @brief Iterate the free list from root, find the best free block
 * in given range. If there is no suitable block, then return NULL.
 * @param[in] The size of free block it requests
 * @param[out] The address of the best free block.
 */
static block_t *better_fit(word_t asize, size_t index) {
    if (index == 0 && root[index] != NULL)
        return first_fit(asize, index);

    for (size_t i = index; i < SEG_SIZE; i++) {
        if (root[i] == NULL)
            continue;

        block_t *block = root[i];
        block_t *best_block = NULL;
        word_t min_diff = UINT64_MAX, cur_size;
        int count = 0;

        do {
            count++;
            cur_size = get_size(block);
            if (asize <= cur_size) {
                if (cur_size - asize < min_diff) {
                    min_diff = cur_size - asize;
                    best_block = block;
                }
            }
            if (count > BETTER_RANGE && best_block != NULL)
                break;
            block = get_next_free(block);
        } while (block != root[i]);

        if (best_block != NULL) {
            if (NEXT_FIT == 1)
                root[i] = best_block;
            return best_block;
        }
    }
    return NULL;
}

/**
 * @brief Print the content in the block, from start block to the last valid
 * block.
 * @param[in] A block in the heap
 */
void print_heap(block_t *start_block) {
    dbg_assert(start_block != NULL);
    block_t *block;
    int count = 0;
    for (block = start_block; get_size(block) > 0; block = find_next(block)) {
        char *status;
        char *prev_status;
        bool is_allocated = get_alloc(block);
        bool is_prev_allocated = extract_prev_alloc(block->header);
        if (is_allocated)
            status = "allocated";
        else
            status = "free     ";
        if (is_prev_allocated)
            prev_status = "allocated";
        else
            prev_status = "free     ";

        word_t size = get_size(block);

        dbg_printf(
            "-----------------------------------------------------------"
            "---------------------------------------------------------\n");
        dbg_printf(
            " Previous Status: %s         Block:%p           Status: %s      "
            "Size: %7ld      Num: %d \n",
            prev_status, block, status, size, count++);
        if (is_allocated == false) {
            block_t *prev_free = get_prev_free(block);
            block_t *next_free = get_next_free(block);
            if (size > min_block_size) {
                dbg_printf(" Previous Free: %p      Next "
                           "Free: %p      Header:0x%lx\n",
                           prev_free, next_free, block->header);
            } else {
                dbg_printf(" Next Free: %p      Header:0x%lx\n", next_free,
                           block->header);
            }
        }
        dbg_printf(
            "-----------------------------------------------------------"
            "---------------------------------------------------------\n");
        dbg_printf("\n");
    }
}

/*
 * ---------------------------------------------------------------------------
 *                           END MY FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/

/**
 * @brief coalesce adjecent free blocks
 * @param[in] block
 * @return
 */
static block_t *coalesce_block(block_t *block) {
    dbg_requires(!get_alloc(block));

    word_t next_header = (find_next(block))->header;
    bool prev_alloc = extract_prev_alloc(block->header);
    bool next_alloc = extract_alloc(next_header);
    size_t cur_size = get_size(block);

    // Case 1: if previous block and next block are allocated blocks.
    if (prev_alloc == true && next_alloc == true) {
        dbg_printf("Case 1 is called.\n");
    }

    // Case 2: if previous block is an allocated block, next block is a free
    // block.
    if (prev_alloc == true && next_alloc == false) {
        dbg_printf("Case 2 is called.\n");
        size_t next_size = extract_size(next_header);
        block_t *next_block = find_next(block);
        remove_free(next_block);
        write_block(block, cur_size + next_size, false, false, 0);
    }

    // Case 3: if previous block is a free block, next block is an allocated
    // block.
    if (prev_alloc == false && next_alloc == true) {
        dbg_printf("Case 3 is called.\n");
        block_t *prev_block = find_prev(block);
        size_t prev_size = extract_size(prev_block->header);
        remove_free(prev_block);
        write_block(prev_block, prev_size + cur_size, false, false, 0);
        block = prev_block;
    }

    // Case 4: if previous block and next block are free blocks.
    if (prev_alloc == false && next_alloc == false) {
        dbg_printf("Case 4 is called.\n");
        size_t next_size = extract_size(next_header);
        block_t *prev_block = find_prev(block);
        block_t *next_block = find_next(block);
        size_t prev_size = extract_size(prev_block->header);
        // Remove next_free and prev_free from the list
        remove_free(prev_block);
        remove_free(next_block);

        write_block(prev_block, prev_size + cur_size + next_size, false, false,
                    0);
        block = prev_block;
    }

    // Insert a free block in the list
    insert_free_block(block);
    return block;
}

/**
 * @brief Extend the heap by the input size when space is not enough
 * @param[in] size
 * @return
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }

    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_block(block, size, false, true, 0);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);

    return block;
}

/**
 * @brief After allocating a block, split it into an allocated block and a free
 * block in order to minimize the internal fraction, when it's possible
 * @param[in] block
 * @param[in] asize
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));
    dbg_requires(asize >= min_block_size);

    size_t block_size = get_size(block);

    if ((block_size - asize) >= min_block_size) {
        remove_free(block);
        write_block(block, asize, true, false, 1);

        block_t *block_next = find_next(block);
        write_block(block_next, block_size - asize, false, false, 2);

        insert_free_block(block_next);
    } else {
        remove_free(block);
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief Find a appropriate free block by a certern algorithm
 * @param[in] asize
 * @return
 */
static block_t *find_fit(size_t asize) {
    size_t index = get_root_index(asize);

    if (FIT_TYPE == 0)
        return first_fit(asize, index);
    else if (FIT_TYPE == 1)
        return best_fit(asize, index);
    else
        return better_fit(asize, index);
}

/**
 * @brief After each operation, check whether the heap is in normal state
 * @param[in] line
 * @return
 */
bool mm_checkheap(int line) {
    // Check for prologue block.
    block_t *block;
    word_t prologue = *(find_prev_footer(heap_start));
    bool block_alloc = extract_alloc(prologue);
    size_t block_size = extract_size(prologue);
    if (block_alloc == 0 || block_size != 0) {
        dbg_printf("Checkheap called at line %d\n", line);
        dbg_printf("Prologue is incorrect: alloc = %d, size = %lu\n",
                   block_alloc, block_size);
        return false;
    }

    word_t prev_header = prologue, cur_header = heap_start->header;
    bool prev_alloc = extract_alloc(prologue);
    for (block = heap_start; get_size(block) > 0; block = find_next(block)) {

        word_t next_header = (find_next(block))->header;
        bool cur_alloc = extract_alloc(cur_header);
        size_t cur_size = extract_size(cur_header);

        // Check each block's address alignment.
        if ((size_t)header_to_payload(block) % dsize != 0) {
            dbg_printf("Checkheap called at line %d\n", line);
            dbg_printf("This block address doesn't align address: %p\n", block);
            return false;
        }

        // Check size meets the minimum size requirement
        if (cur_size < min_block_size) {
            dbg_printf("Checkheap called at line %d\n", line);
            dbg_printf("Current block size is below the minimum size, cur_size "
                       "= %lu\n",
                       cur_size);
            return false;
        }

        // Check blocks lie within heap boundaries.
        void *low = mem_heap_lo(), *high = mem_heap_hi();
        void *prev_free = get_prev_free(block),
             *next_free = get_next_free(block);
        if (cur_alloc == false && cur_size > min_block_size) {
            bool flag = true;

            // Check next free block
            if (next_free < low || next_free > high) {
                dbg_printf("Next free block: %p is out of boundaries\n",
                           next_free);
                flag = false;
            }

            // Check previous free block
            if (prev_free < low || prev_free > high) {
                dbg_printf("Previous free block: %p is out of boundaries\n",
                           prev_free);
                flag = false;
            }

            if (flag == false) {
                dbg_printf("Heap low: %p, heap high: %p\n", low, high);
                return false;
            }
        }

        // Check header and footer matching each other
        if (cur_alloc == 0 && cur_size > min_block_size) {
            word_t cur_footer = *(header_to_footer(block));
            if (cur_header != cur_footer) {
                dbg_printf("Checkheap called at line %d\n", line);
                dbg_printf("Header and footer don't match, cur_header = %lx, "
                           "cur_footer = %lx\n",
                           cur_header, cur_footer);
                return false;
            }
        }

        // Check coalescing: no consecutive free blocks in the heap.
        if (prev_alloc == 0 && cur_alloc == 0) {
            dbg_printf("Checkheap called at line %d\n", line);
            dbg_printf("Consecutive free blocks in the heap");
            return false;
        }

        // check previous/next allocate/free bit consistency.
        // if (extract_size(prev_header) > 0) {
        if (prev_alloc != extract_prev_alloc(cur_header)) {
            dbg_printf("Checkheap called at line %d\n", line);
            dbg_printf("Previous/next allocate/free bit inconsistency\n");
            return false;
        }
        // }

        // update prev_footer, cur_header, prev_alloc for next.
        prev_header = cur_header;
        prev_alloc = cur_alloc;
        cur_header = next_header;
    }

    // Check for epilogue block.
    block_alloc = extract_alloc(cur_header);
    block_size = extract_size(cur_header);
    if (block_alloc == 0 || block_size != 0) {
        dbg_printf("Checkheap called at line %d\n", line);
        dbg_printf("epilogue is incorrect: alloc = %d, size = %lu\n",
                   block_alloc, block_size);
        return false;
    }

    return true;
}

/**
 * @brief Initialization before using any operation
 * @return
 */
bool mm_init(void) {
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    for (size_t i = 0; i < SEG_SIZE; i++) {
        root[i] = NULL;
    }

    start[0] = pack(0, true, false, false); // Heap prologue (block footer)
    start[1] = pack(0, true, false, false); // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);

    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL) {
        return false;
    }

    // Insert a free block in the list
    insert_free_block(heap_start);

    dbg_printheap(heap_start);

    return true;
}

/**
 * @brief Request space from memory for given size
 * @param[in] size
 * @return
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        mm_init();
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = round_up(size + wsize, dsize);

    // Search the free list for a fit
    // Use no boundry tag here
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL) {
        // Always request at least chunksize
        extendsize = max(asize, chunksize);
        block = extend_heap(extendsize);

        // extend_heap returns an error
        if (block == NULL) {
            return bp;
        }
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(block));

    // Mark block as allocated
    size_t block_size = get_size(block);
    write_block(block, block_size, true, false, 0);

    // Try to split the block if too large
    split_block(block, asize);

    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    dbg_printheap(heap_start);
    return bp;
}

/**
 * @brief Free the space of the block in heap that is previously allocated
 * @param[in] bp
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_block(block, size, false, false, 0);

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);

    dbg_ensures(mm_checkheap(__LINE__));
    dbg_printheap(heap_start);
}

/**
 * @brief Adjust the space of the block in heap that is previously allocated
 * @param[in] ptr
 * @param[in] size
 * @return
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);

    return newptr;
}

/**
 * @brief Request space from memory by the number of element and its size
 * @param[in] elements
 * @param[in] size
 * @return
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */
