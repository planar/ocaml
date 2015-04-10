/***********************************************************************/
/*                                                                     */
/*                                OCaml                                */
/*                                                                     */
/*             Damien Doligez, projet Para, INRIA Rocquencourt         */
/*                                                                     */
/*  Copyright 1996 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Library General Public License, with    */
/*  the special exception on linking described in file ../LICENSE.     */
/*                                                                     */
/***********************************************************************/

#define FREELIST_DEBUG 0
#if FREELIST_DEBUG
#include <stdio.h>
#endif

#include <string.h>

#include "config.h"
#include "freelist.h"
#include "gc.h"
#include "gc_ctrl.h"
#include "memory.h"
#include "major_gc.h"
#include "misc.h"
#include "mlvalues.h"

/* The free-lists are kept sorted by increasing addresses.
   This makes the merging of adjacent free blocks possible.
   (See [caml_fl_merge_block].)
*/

typedef struct {
  char *next_bp;   /* Pointer to the first byte of the next block. */
} block;

/* The sentinels can be located anywhere in memory, but they must not be
   adjacent to any heap object. */
struct sentinel {
  value filler1;
  header_t h;
  value first_bp;
  value filler2;
};
#define MAX_SMALL_LIST_WOSZ 20
/* The size is one more than the max: element 0 is the normal free list. */
#define NUM_FREE_LISTS (MAX_SMALL_LIST_WOSZ + 1)
static struct sentinel sentinels[NUM_FREE_LISTS] = {
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
  {0, Make_header (1, 0, Caml_blue), 0, 0},
};

#define Fl_head(i) ((char *) (&(sentinels[i].first_bp)))

/* Current allocation pointer in main list. */
static char *fl_prev = Fl_head(0);

uintnat caml_fl_small_max = 5;

/* Last block in the main list. Only valid just after [caml_fl_allocate]
   returns NULL. */
static char *fl_last = NULL;

/* Current insertion pointers. Managed jointly with [sweep_slice]. */
char *caml_fl_merge[NUM_FREE_LISTS];
char *caml_fl_merge_prev = NULL;

/* Number of words in the free lists, including headers but not fragments. */
asize_t caml_fl_cur_size = 0;

/* data structures for the first-fit policy */
#define FLP_MAX 1000
static char *flp [FLP_MAX];
static int flp_size = 0;
static char *beyond = NULL;

#define Next(b) (((block *) (b))->next_bp)

#define Policy_next_fit 0
#define Policy_first_fit 1
uintnat caml_allocation_policy = Policy_next_fit;
#define policy caml_allocation_policy

#ifdef DEBUG
static void fl_check (void)
{
  char *cur, *prev;
  int prev_found = 0, flp_found = 0;
  int merge_found;
  uintnat size_found = 0;
  int sz = 0;
  int list;

  for (list = 0; list <= caml_fl_small_max; list++){
    merge_found = 0;
    prev = Fl_head(list);
    cur = Next (prev);
    while (cur != NULL){
      size_found += Whsize_bp (cur);
      Assert (Is_in_heap (cur));
      if (list == 0){
        if (cur == fl_prev) prev_found = 1;
        if (policy == Policy_first_fit && Wosize_bp (cur) > sz){
          sz = Wosize_bp (cur);
          if (flp_found < flp_size){
            Assert (Next (flp[flp_found]) == cur);
            ++ flp_found;
          }else{
            Assert (beyond == NULL || cur >= Next (beyond));
          }
        }
      }else{
        CAMLassert (Wosize_bp (cur) == list);
        if (prev != Fl_head(list) && Color_bp (prev) == Caml_blue){
          CAMLassert (Color_bp (cur) == Caml_blue);
          CAMLassert (cur > prev);
        }else{
          CAMLassert (Color_bp (cur) == Caml_blue
                      || Color_bp (cur) == Caml_white);
        }
      }
      if (cur == caml_fl_merge[list]) merge_found = 1;
      prev = cur;
      cur = Next (prev);
    }
    CAMLassert (merge_found || caml_fl_merge[list] == Fl_head(list));
  }
  if (policy == Policy_next_fit) Assert (prev_found || fl_prev == Fl_head(0));
  if (policy == Policy_first_fit) Assert (flp_found == flp_size);
  Assert (size_found == caml_fl_cur_size);
}

#endif

/* [allocate_block] is called by [caml_fl_allocate].  Given a suitable free
   block and the desired size [wh_sz], it allocates a new block from the
   free block. There are four cases:
   0. The free block has size [wh_sz]. Detach the block from its
      free list and return it.
   1. The free block is 1 word longer than [wh_sz].  Detach the block
      from its free list. The remaining word cannot be linked:
      turn it into a fragment and return the rest.
   2. The free block's size is between [wh_sz+1] and [wh_sz+caml_fl_small_max].
      Detach it from its free list, split it in two and return the high
      block. Cons the low block to the corresponding free list, with the
      correct color.
   3. The free block is larger than [wh_sz+caml_fl_small_max]. Split it
      in two and return the high block.
   In all cases, the allocated block is right-justified in the free block:
   it is located in the high-address words of the free block. This way,
   the linking of the free-list does not change in case 3.
*/
static char *allocate_block (mlsize_t wh_sz, int flpi, char *prev, char *cur)
{
  header_t h = Hd_bp (cur);
  mlsize_t cur_wosz = Wosize_hd (h);
  int list = (cur_wosz > caml_fl_small_max) ? 0 : cur_wosz;
                                             Assert (Whsize_hd (h) >= wh_sz);
  if (cur_wosz < wh_sz + 1){                        /* Cases 0 and 1. */
    caml_fl_cur_size -= Whsize_wosize (cur_wosz);
    Next (prev) = Next (cur);
                    Assert (Is_in_heap (Next (prev)) || Next (prev) == NULL);
    if (caml_fl_merge[list] == cur) caml_fl_merge[list] = prev;
    if (caml_fl_merge_prev == cur) caml_fl_merge_prev = NULL;
#ifdef DEBUG
    fl_last = NULL;
#endif
      /* In case 1, the following creates the empty block correctly.
         In case 0, it gives an invalid header to the block.  The function
         calling [caml_fl_allocate] will overwrite it. */
    Hd_op (cur) = Make_header (0, 0, Caml_white);
    if (policy == Policy_first_fit){
      if (flpi + 1 < flp_size && flp[flpi + 1] == cur){
        flp[flpi + 1] = prev;
      }else if (flpi == flp_size - 1){
        beyond = (prev == Fl_head(0)) ? NULL : prev;
        -- flp_size;
      }
    }
  }else{                                                 /* Cases 2 and 3. */
    mlsize_t remwosz = cur_wosz - wh_sz;
    caml_fl_cur_size -= wh_sz;
    if (remwosz > caml_fl_small_max){
      Hd_op (cur) = Make_header (remwosz, 0, Caml_blue);
    }else{
      if (caml_fl_merge[0] == cur) caml_fl_merge[0] = prev;
      Next (prev) = Next (cur);
      if (fl_prev == cur) fl_prev = Next (fl_prev);
      Hd_op (cur) = Make_header (remwosz, Abstract_tag, Caml_white);
      if (caml_gc_phase == Phase_sweep){
        /* Do not insert into free list */
        if (caml_fl_merge_prev == cur) caml_fl_merge_prev = NULL;
        caml_fl_cur_size -= Whsize_wosize (remwosz);
#ifdef DEBUG
        Next (cur) = NULL;
#endif
      }else{
        Next (cur) = Next (Fl_head (remwosz));
        Next (Fl_head (remwosz)) = cur;
      }
    }
  }
  if (policy == Policy_next_fit) fl_prev = prev;
  return cur + Bsize_wsize (cur_wosz - wh_sz);
}

/* [caml_fl_allocate] does not set the header of the newly allocated block.
   The calling function must do it before any GC function gets called.
   [caml_fl_allocate] returns a head pointer.
*/
char *caml_fl_allocate (mlsize_t wo_sz)
{
  char *cur = NULL, *prev, *result;
  int i;
  mlsize_t sz, prevsz;
                                  Assert (sizeof (char *) == sizeof (value));
                                  Assert (wo_sz >= 1);
  if (wo_sz <= caml_fl_small_max){
    result = Next (Fl_head (wo_sz));
    if (result != NULL){
      Next (Fl_head (wo_sz)) = Next (result);
      caml_fl_cur_size -= Whsize_wosize (wo_sz);
      if (result == caml_fl_merge_prev) caml_fl_merge_prev = NULL;
      if (result == caml_fl_merge[wo_sz]){
        caml_fl_merge[wo_sz] = Fl_head (wo_sz);
      }
      return Hp_op (result);
    }
    /* Fall through to generic allocation. We could also try to allocate
       from another small free-list of larger size. */
  }
  switch (policy){
  case Policy_next_fit:
                                  Assert (fl_prev != NULL);
    /* Search from [fl_prev] to the end of the list. */
    prev = fl_prev;
    cur = Next (prev);
    while (cur != NULL){                             Assert (Is_in_heap (cur));
      if (Wosize_bp (cur) >= wo_sz){
        return allocate_block (Whsize_wosize (wo_sz), 0, prev, cur);
      }
      prev = cur;
      cur = Next (prev);
    }
    fl_last = prev;
    /* Search from the start of the list to [fl_prev]. */
    prev = Fl_head (0);
    cur = Next (prev);
    while (prev != fl_prev){
      if (Wosize_bp (cur) >= wo_sz){
        return allocate_block (Whsize_wosize (wo_sz), 0, prev, cur);
      }
      prev = cur;
      cur = Next (prev);
    }
    /* No suitable block was found. */
    return NULL;
    break;

  case Policy_first_fit: {
    /* Search in the flp array. */
    for (i = 0; i < flp_size; i++){
      sz = Wosize_bp (Next (flp[i]));
      if (sz >= wo_sz){
        result = allocate_block (Whsize_wosize (wo_sz), i, flp[i],
                                 Next (flp[i]));
        goto update_flp;
      }
    }
    /* Extend the flp array. */
    if (flp_size == 0){
      prev = Fl_head (0);
      prevsz = 0;
    }else{
      prev = Next (flp[flp_size - 1]);
      prevsz = Wosize_bp (prev);
      if (beyond != NULL) prev = beyond;
    }
    while (flp_size < FLP_MAX){
      cur = Next (prev);
      if (cur == NULL){
        fl_last = prev;
        beyond = (prev == Fl_head (0)) ? NULL : prev;
        return NULL;
      }else{
        sz = Wosize_bp (cur);
        if (sz > prevsz){
          flp[flp_size] = prev;
          ++ flp_size;
          if (sz >= wo_sz){
            beyond = cur;
            i = flp_size - 1;
            result = allocate_block (Whsize_wosize (wo_sz), flp_size - 1, prev,
                                     cur);
            goto update_flp;
          }
          prevsz = sz;
        }
      }
      prev = cur;
    }
    beyond = cur;

    /* The flp table is full.  Do a slow first-fit search. */
    if (beyond != NULL){
      prev = beyond;
    }else{
      prev = flp[flp_size - 1];
    }
    prevsz = Wosize_bp (Next (flp[FLP_MAX-1]));
    Assert (prevsz < wo_sz);
    cur = Next (prev);
    while (cur != NULL){
      Assert (Is_in_heap (cur));
      sz = Wosize_bp (cur);
      if (sz < prevsz){
        beyond = cur;
      }else if (sz >= wo_sz){
        return allocate_block (Whsize_wosize (wo_sz), flp_size, prev, cur);
      }
      prev = cur;
      cur = Next (prev);
    }
    fl_last = prev;
    return NULL;

  update_flp: /* (i, sz) */
    /* The block at [i] was removed or reduced.  Update the table. */
    Assert (0 <= i && i < flp_size + 1);
    if (i < flp_size){
      if (i > 0){
        prevsz = Wosize_bp (Next (flp[i-1]));
      }else{
        prevsz = 0;
      }
      if (i == flp_size - 1){
        if (Wosize_bp (Next (flp[i])) <= prevsz){
          beyond = Next (flp[i]);
          -- flp_size;
        }else{
          beyond = NULL;
        }
      }else{
        char *buf [FLP_MAX];
        int j = 0;
        mlsize_t oldsz = sz;

        prev = flp[i];
        while (prev != flp[i+1]){
          cur = Next (prev);
          sz = Wosize_bp (cur);
          if (sz > prevsz){
            buf[j++] = prev;
            prevsz = sz;
            if (sz >= oldsz){
              Assert (sz == oldsz);
              break;
            }
          }
          prev = cur;
        }
        if (FLP_MAX >= flp_size + j - 1){
          if (j != 1){
            memmove (&flp[i+j], &flp[i+1], sizeof (block *) * (flp_size-i-1));
          }
          if (j > 0) memmove (&flp[i], &buf[0], sizeof (block *) * j);
          flp_size += j - 1;
        }else{
          if (FLP_MAX > i + j){
            if (j != 1){
              memmove (&flp[i+j], &flp[i+1], sizeof (block *) * (FLP_MAX-i-j));
            }
            if (j > 0) memmove (&flp[i], &buf[0], sizeof (block *) * j);
          }else{
            if (i != FLP_MAX){
              memmove (&flp[i], &buf[0], sizeof (block *) * (FLP_MAX - i));
            }
          }
          flp_size = FLP_MAX - 1;
          beyond = Next (flp[FLP_MAX - 1]);
        }
      }
    }
    return result;
  }
  break;

  default:
    Assert (0);   /* unknown policy */
    break;
  }
  return NULL;  /* NOT REACHED */
}

/* Drop the temp part of the small free lists and initialize the merge
   variables. */
void caml_fl_init_merge (void)
{
  int i;
  for (i = 1; i <= caml_fl_small_max; i++){
    while (Next (Fl_head (i)) != NULL && Is_white_val (Next (Fl_head (i)))){
      Next (Fl_head (i)) = Next (Next (Fl_head (i)));
      caml_fl_cur_size -= Whsize_wosize (i);
    }
    caml_fl_merge[i] = Fl_head (i);
  }
  caml_fl_merge[0] = Fl_head (0);
#ifdef DEBUG
  fl_check ();
#endif
}

static void truncate_flp (char *changed)
{
  if (changed == Fl_head (0)){
    flp_size = 0;
    beyond = NULL;
  }else{
    while (flp_size > 0 && Next (flp[flp_size - 1]) >= changed) -- flp_size;
    if (beyond >= changed) beyond = NULL;
  }
}

/* This is called by caml_compact_heap. */
void caml_fl_reset (void)
{
  int i;
  for (i = 0; i <= caml_fl_small_max; i++){
    Next (Fl_head(i)) = NULL;
  }
  switch (policy){
  case Policy_next_fit:
    fl_prev = Fl_head (0);
    break;
  case Policy_first_fit:
    truncate_flp (Fl_head (0));
    break;
  default:
    Assert (0);
    break;
  }
  caml_fl_cur_size = 0;
  caml_fl_init_merge ();
}

/* [caml_fl_merge_block] returns a pointer to the current block, which
   may have moved because of merging.
*/
char *caml_fl_merge_block (char *bp)
{
  char *right, *prev;
  mlsize_t wosz = Wosize_bp (bp), new_wosz, left_wosz;
  int list;

  caml_fl_cur_size += Whsize_wosize (wosz);

  if (policy == Policy_first_fit) truncate_flp (caml_fl_merge[0]);

#ifdef DEBUG
  caml_set_fields (bp, 0, Debug_free_major);
#endif

  if (caml_fl_merge_prev != NULL
      && caml_fl_merge_prev + Bhsize_bp (caml_fl_merge_prev) == bp){
    /* The block to the left is free, merge it. */
    left_wosz = Wosize_bp (caml_fl_merge_prev);
    new_wosz = wosz + Whsize_wosize (left_wosz);
    if (new_wosz <= Max_wosize){
#ifdef DEBUG
      Hd_bp (bp) = Debug_free_major;
#endif
      if (Color_bp (caml_fl_merge_prev) == Caml_blue){
        /* remove it from its free list */
        list = (left_wosz > caml_fl_small_max) ? 0 : left_wosz;
        prev = caml_fl_merge[list];
        CAMLassert (Next (prev) == caml_fl_merge_prev);
        Next (prev) = Next (caml_fl_merge_prev);
      }else{
        CAMLassert (left_wosz == 0);
        ++ caml_fl_cur_size;
      }
      wosz = new_wosz;
      bp = caml_fl_merge_prev;
      caml_fl_merge_prev = NULL;
    }
  }

  right = bp + Bhsize_wosize (wosz);
  if (Color_bp (right) == Caml_blue){
    /* If the right block is in a free list, remove it and merge it. */
    int right_wosz = Wosize_bp (right);
    list = (right_wosz > caml_fl_small_max) ? 0 : right_wosz;
    prev = caml_fl_merge[list];
    CAMLassert (Next (prev) == right);
    new_wosz = wosz + Whsize_wosize (right_wosz);
    if (new_wosz <= Max_wosize){
      Next (prev) = Next (right);
      wosz = new_wosz;
    }
  }

  if (wosz > 0){
    char *nextprev;
    /* Set the correct header and insert in the correct free list */
    list = (wosz > caml_fl_small_max) ? 0 : wosz;
    Hd_bp (bp) = Make_header (wosz, Abstract_tag, Caml_blue);
    prev = caml_fl_merge[list];
    nextprev = Next (prev);
    if (nextprev != NULL && nextprev == caml_fl_merge_prev){
      prev = caml_fl_merge_prev;
    }
    Next (bp) = Next (prev); /* /!\ not [nextprev] */
    Next (prev) = bp;
  }else{
    /* If wosz == 0, this is a fragment. Leave it in white. */
    caml_fl_cur_size -= Whsize_wosize (0);
  }
  return bp;
}

/* This is a heap extension.  We have to insert it in the right place
   in the free-list.
   [caml_fl_add_blocks] can only be called right after a call to
   [caml_fl_allocate] that returned NULL.
   Most of the heap extensions are expected to be at the end of the
   free list.  (This depends on the implementation of [malloc].)

   [bp] must point to a list of blocks chained by their field 0,
   terminated by NULL, and field 1 of the first block must point to
   the last block.

   All blocks must be larger than caml_fl_small_max.
*/
void caml_fl_add_blocks (char *bp)
{
                                                   Assert (fl_last != NULL);
                                            Assert (Next (fl_last) == NULL);
  caml_fl_cur_size += Whsize_bp (bp);

  if (bp > fl_last){
    Next (fl_last) = bp;
    if (fl_last == caml_fl_merge[0] && bp < caml_gc_sweep_hp){
      caml_fl_merge[0] = (char *) Field (bp, 1);
    }
    if (policy == Policy_first_fit && flp_size < FLP_MAX){
      flp [flp_size++] = fl_last;
    }
  }else{
    char *cur, *prev;

    prev = Fl_head (0);
    cur = Next (prev);
    while (cur != NULL && cur < bp){
      CAMLassert (prev < bp || prev == Fl_head (0));
      /* XXX TODO: extend flp on the fly */
      prev = cur;
      cur = Next (prev);
    }
    CAMLassert (prev < bp || prev == Fl_head (0));
    CAMLassert (cur > bp || cur == NULL);
    Next (Field (bp, 1)) = cur;
    Next (prev) = bp;
    /* When inserting blocks between [caml_fl_merge] and [caml_gc_sweep_hp],
       we must advance [caml_fl_merge] to the new block, so that [caml_fl_merge]
       is always the last free-list block before [caml_gc_sweep_hp]. */
    if (prev == caml_fl_merge[0] && bp < caml_gc_sweep_hp){
      caml_fl_merge[0] = (char *) Field (bp, 1);
    }
    if (policy == Policy_first_fit) truncate_flp (bp);
  }
}

/* Cut a block of memory into Max_wosize pieces, give them headers,
   and optionally merge them into the free list.
   arguments:
   p: pointer to the first word of the block
   size: size of the block (in words)
   do_merge: 1 -> do merge; 0 -> do not merge
   color: which color to give to the pieces; if [do_merge] is 1, this
          is overridden by the merge code, but we have historically used
          [Caml_white].
*/
void caml_make_free_blocks (value *p, mlsize_t size, int do_merge, int color)
{
  mlsize_t sz;

  while (size > 0){
    if (size > Whsize_wosize (Max_wosize)){
      sz = Whsize_wosize (Max_wosize);
    }else{
      sz = size;
    }
    *(header_t *)p = Make_header (Wosize_whsize (sz), 0, color);
    if (do_merge){
      caml_fl_merge_prev = NULL;
      caml_fl_merge_block (Bp_hp (p));
    }
    size -= sz;
    p += sz;
  }
}

void caml_set_allocation_policy (uintnat p)
{
  switch (p){
  case Policy_next_fit:
    fl_prev = Fl_head (0);
    policy = p;
    break;
  case Policy_first_fit:
    flp_size = 0;
    beyond = NULL;
    policy = p;
    break;
  default:
    break;
  }
}
