/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
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
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
#define debug(...) printf(__VA_ARGS__)
#else
#define debug(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

typedef struct {
  int32_t header;
  /*
   * We don't know what the size of the payload will be, so we will
   * declare it as a zero-length array.  This allow us to obtain a
   * pointer to the start of the payload.
   */
  uint8_t payload[];
} block_t;

static size_t chunksize = 0;
static size_t mem_heap_high = 0;
static block_t *heap_listp = NULL;

static size_t round_up(size_t size) {
  return (size + ALIGNMENT - 1) & -ALIGNMENT;
}

static size_t get_size(block_t *block) {
  return block->header & -2;
}

static void set_header_footer(block_t *block, size_t size, bool is_allocated) {
  int32_t val = size | is_allocated;
  block->header = val;
  size_t footer = (size_t)block + size - sizeof(block_t);
  *(int32_t *)(footer) = val;
}

static int32_t get_header(block_t *block) {
  return block->header;
}

static void *get_next_block(block_t *block) {
  size_t size = get_size(block);
  if ((long)(block) + size + 16 <= mem_heap_high) {
    return (void *)((long)(block) + size);
  }

  return NULL;
}

static void *get_prev_block(block_t *block) {
  if ((long)(block)-16 > (long)(heap_listp)) {
    void *prev_block_footer = (void *)block - sizeof(block_t);
    size_t size = get_size(prev_block_footer);

    return (void *)((long)(block)-size);
  }

  return NULL;
}

static bool get_alloc(block_t *block) {
  if (block == NULL) {
    return true;
  }

  int32_t res = get_header(block) & 1;
  return res;
}

/*
 * mm_init - Called when a new trace starts.
 */
int mm_init(void) {
  /* Pad heap start so first payload is at ALIGNMENT. */
  if ((long)mem_sbrk(ALIGNMENT - sizeof(block_t)) < 0)
    return -1;

  size_t size = round_up(2);
  heap_listp = mem_sbrk(size);
  mem_heap_high = (long)heap_listp + size;

  set_header_footer(heap_listp, size, false);

  chunksize = 1 << 7;

  return 0;
}

static void *find_fit(size_t size) {
  block_t *fit_block = NULL;
  block_t *work_block = heap_listp;
  size_t fit_size = 0;
  size_t work_size;

  while ((work_block = get_next_block(work_block)) != NULL) {
    if (!get_alloc(work_block)) {
      work_size = get_size(work_block);
      if (work_size >= size) {
        if (fit_block == NULL || work_size < fit_size) {
          fit_block = work_block;
          fit_size = work_size;
        }
      }
    }
  }

  if (fit_block != NULL) {
    size_t diff = fit_size - size;
    if (diff >= 16) {
      block_t *new_free = (block_t *)((long)fit_block + size);
      set_header_footer(new_free, diff, false);
    }

    set_header_footer(fit_block, size, true);
  }

  return fit_block;
}

static void *increase(size_t size) {
  void *ptr;
  chunksize = size > chunksize ? size : chunksize;
  size_t diff = chunksize - size;

  if (diff >= 16) {
    ptr = mem_sbrk(chunksize);
    if ((long)ptr > 0) {
      mem_heap_high += chunksize;
      set_header_footer(ptr + size, diff, false);

      return ptr;
    }
  }

  ptr = mem_sbrk(size);
  if ((long)ptr > 0) {
    mem_heap_high += size;

    return ptr;
  }

  return (void *)(-1);
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size) {
  size = round_up((2 * sizeof(block_t)) + size);
  // printf("Malloc: %ld\n", size);
  block_t *block;

  if ((block = find_fit(size)) != NULL) {
    return block->payload;
  }

  block = increase(size);
  if ((long)block < 0)
    return NULL;

  set_header_footer(block, size, true);

  return block->payload;
}

static void *coalesce(block_t *block) {
  block_t *prev_block = get_prev_block(block);
  block_t *next_block = get_next_block(block);
  bool prev_alloc = get_alloc(prev_block);
  bool next_alloc = get_alloc(next_block);
  size_t size = get_size(block);

  if (prev_alloc && next_alloc) {
    // printf("No coalescing\n");
    return block;
  } else if (prev_alloc && !next_alloc) {
    // printf("Coalescing right\n");
    size += get_size(next_block);
    set_header_footer(block, size, false);
  } else if (!prev_alloc && next_alloc) {
    // printf("Coalescing left\n");
    size += get_size(prev_block);
    block = prev_block;
    set_header_footer(block, size, false);
  } else {
    // printf("Coalescing both\n");
    size += get_size(next_block) + get_size(prev_block);
    block = prev_block;
    set_header_footer(block, size, false);
  }

  return block;
}

/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
void free(void *ptr) {
  if (ptr != NULL) {
    block_t *block = ptr - sizeof(block_t);
    size_t size = get_size(block);

    set_header_footer(block, size, false);
    // set_footer(block, size, false);

    block = coalesce(block);
  }
}

// ptr must be a block, not payload
static bool try_expand(void *block, size_t size) {
  size_t csize = get_size(block);

  if (csize - (2 * sizeof(block_t)) >= size) {
    return true;
  }

  block_t *next_block = get_next_block(block);
  bool next_alloc = get_alloc(next_block);
  size = round_up(size + (2 * sizeof(block_t)));
  (void)next_alloc;

  if (next_block == NULL) {
    increase(size - csize);
    set_header_footer(block, size, true);

    return true;
  } else if (!next_alloc) {
    size_t next_size = get_size(next_block);
    if (csize + next_size >= size) {
      size_t diff = csize + next_size - size;
      if (diff >= 16) {
        set_header_footer(block + size, diff, false);
      }

      set_header_footer(block, size + diff, true);
      return true;
    }
  }

  return false;
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.
 **/
void *realloc(void *old_ptr, size_t size) {
  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);

  if (try_expand(old_ptr - sizeof(block_t), size)) {
    return old_ptr;
  }

  void *new_ptr = malloc(size);

  /* If malloc() fails, the original block is left untouched. */
  if (!new_ptr)
    return NULL;

  /* Copy the old data. */
  block_t *block = old_ptr - offsetof(block_t, payload);
  size_t old_size = get_size(block);
  if (size < old_size)
    old_size = size;
  memcpy(new_ptr, old_ptr, old_size);

  /* Free the old block. */
  free(old_ptr);

  return new_ptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);

  /* If malloc() fails, skip zeroing out the memory. */
  if (new_ptr)
    memset(new_ptr, 0, bytes);

  return new_ptr;
}

/*
 * mm_checkheap - So simple, it doesn't need a checker!
 */
void mm_checkheap(int verbose) {
}
