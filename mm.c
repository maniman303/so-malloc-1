/* Michał Wójtowicz 308248 oświadczam że jestem jedynym autorem kodu źrodłowego.
W swoim rozwiązaniu zawarłem adaptację częściowego rozwiązania z książki
CSAPP 9.9. Zaimplementowałem z wykorzystaniem boundary tags metodę best fit z
gorliwym kompaktowaniem wolnych bloków podczas free.
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

static inline void *coalesce(block_t *);

static size_t round_up(size_t size) {
  return (size + ALIGNMENT - 1) & -ALIGNMENT;
}

static size_t get_size(block_t *block) {
  return block->header & -2;
}

static inline void set_header_footer(block_t *block, size_t size,
                                     bool is_allocated) {
  int32_t val = size | is_allocated;
  block->header = val;
  size_t footer = (size_t)block + size - sizeof(block_t);
  *(int32_t *)(footer) = val;
}

static inline int32_t get_header(block_t *block) {
  return block->header;
}

static inline void *get_next_block(block_t *block) {
  size_t size = get_size(block);
  if ((long)(block) + size + 16 <= mem_heap_high) {
    return (void *)((long)(block) + size);
  }

  return NULL;
}

static inline void *get_prev_block(block_t *block) {
  if ((long)(block)-16 > (long)(heap_listp)) {
    void *prev_block_footer = (void *)block - sizeof(block_t);
    size_t size = get_size(prev_block_footer);

    return (void *)((long)(block)-size);
  }

  return NULL;
}

static inline bool get_alloc(block_t *block) {
  if (block == NULL) {
    return true;
  }

  int32_t res = get_header(block) & 1;
  return res;
}

// Częściowa adaptacja rozwiązania z CSAPP
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

// Best fit - szuka najmniejszego wolnego i pasującego bloku
static inline void *find_fit(size_t size) {
  block_t *fit_block = NULL;
  block_t *work_block = get_next_block(heap_listp);
  size_t fit_size = 0;
  size_t work_size;

  while (work_block != NULL) {
    if (!get_alloc(work_block)) {
      work_size = get_size(work_block);

      if (work_size >= size && (fit_block == NULL || work_size < fit_size)) {
        fit_block = work_block;
        fit_size = work_size;
      }
    }

    work_block = get_next_block(work_block);
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

static inline void *increase(size_t size) {
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

// Adaptacja rozwiązania z CSAPP
static inline void *coalesce(block_t *block) {
  block_t *prev_block = get_prev_block(block);
  block_t *next_block = get_next_block(block);
  bool prev_alloc = get_alloc(prev_block);
  bool next_alloc = get_alloc(next_block);
  size_t size = get_size(block);

  if (prev_alloc && next_alloc) {
    return block;
  } else if (prev_alloc && !next_alloc) {
    size += get_size(next_block);
    set_header_footer(block, size, false);
  } else if (!prev_alloc && next_alloc) {
    size += get_size(prev_block);
    block = prev_block;
    set_header_footer(block, size, false);
  } else {
    size += get_size(next_block) + get_size(prev_block);
    block = prev_block;
    set_header_footer(block, size, false);
  }

  return block;
}

/*
 * free
 */
void free(void *ptr) {
  if (ptr != NULL) {
    block_t *block = ptr - sizeof(block_t);
    size_t size = get_size(block);

    set_header_footer(block, size, false);

    block = coalesce(block);
  }
}

// Próba rozszerzenia już zaalokowanej pamięci
static inline bool try_expand(void *block, size_t size) {
  size_t csize = get_size(block);

  // Sprawdza czy już zaalokowana pamięć razem z paddingiem nie jest
  // wystarczająca
  if (csize - (2 * sizeof(block_t)) >= size) {
    return true;
  }

  block_t *next_block = get_next_block(block);
  bool next_alloc = get_alloc(next_block);
  size_t next_size = next_alloc ? 0 : get_size(next_block);
  size = round_up(size + (2 * sizeof(block_t)));

  // Sprawdza czy blok nie jest ostatni na liście - wtedy starczy poszerzyć
  // stertę
  // W przeciwnym wypadku sprawdza czy blok obok jest pusty i
  // wystarczająco duży
  if (next_block == NULL) {
    increase(size - csize);
    set_header_footer(block, size, true);

    return true;
  } else if (!next_alloc && (csize + next_size >= size)) {
    size_t diff = csize + next_size - size;

    if (diff >= 16) {
      set_header_footer(block + size, diff, false);
    }

    set_header_footer(block, size + diff, true);
    return true;
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

  // Próba rozszerzenia już zaalokowanej pamięci
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
 * mm_checkheap - sprawdza czy nie ma obok siebie dwóch wolnych bloków
 */
void mm_checkheap(int verbose) {
  block_t *work_block = heap_listp;
  bool prev_alloc = false;
  bool work_alloc;

  while ((work_block = get_next_block(work_block)) != NULL) {
    work_alloc = get_alloc(work_block);

    if (!prev_alloc && !work_alloc) {
      exit(-1);
    }

    prev_alloc = work_alloc;
  }
}
