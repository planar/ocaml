/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*              Damien Doligez, projet Para, INRIA Rocquencourt           */
/*                                                                        */
/*   Copyright 1996 Institut National de Recherche en Informatique et     */
/*     en Automatique.                                                    */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

#define CAML_INTERNALS

#define FREELIST_DEBUG 0
#if FREELIST_DEBUG
#include <stdio.h>
#endif

#include <string.h>

#include "caml/config.h"
#include "caml/freelist.h"
#include "caml/gc.h"
#include "caml/gc_ctrl.h"
#include "caml/memory.h"
#include "caml/major_gc.h"
#include "caml/misc.h"
#include "caml/mlvalues.h"

/* quick-fit + FIFO-ordered best fit (Wilson's nomenclature) */

/* NUM_SMALL must be at least 3 for this code to work,
   at least 5 for good performance on typical OCaml programs.
*/
#define NUM_SMALL 32

/* A free list block is a [value] (integer representing a pointer to the
   first word after the block's header). The end of the  list is NULL. */
#define Val_NULL ((value) NULL)

static struct {
  value free;
  value *merge;
} small_fl [NUM_SMALL + 1];

asize_t caml_fl_cur_wsz = 0;     /* Number of words in the free list,
                                    including headers but not fragments. */
value caml_fl_merge = Val_NULL;  /* Current insertion pointer.  Managed
                                    jointly with [sweep_slice]. */

#define Next_small(v) (Field (v, 0))

#define Policy_best_fit 2
uintnat caml_allocation_policy = Policy_best_fit;
#define policy caml_allocation_policy

/* Small free blocks have only one pointer to the next block.
   Large free blocks have 5 fields:
   tree fields:
     - node flag
     - left son
     - right son
   list fields:
     - next
     - prev
*/
typedef struct large_free_block {
  int isnode;
  struct large_free_block *left;
  struct large_free_block *right;
  struct large_free_block *prev;
  struct large_free_block *next;
} large_free_block;
#define size(n) (Wosize_val((value)n))

static struct large_free_block *large_fl;

#ifdef CAML_INSTR
static uintnat instr_size [20] =
  {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
static char *instr_name [20] = {
  NULL,
  "alloc01@",
  "alloc02@",
  "alloc03@",
  "alloc04@",
  "alloc05@",
  "alloc06@",
  "alloc07@",
  "alloc08@",
  "alloc09@",
  "alloc10-19@",
  "alloc20-29@",
  "alloc30-39@",
  "alloc40-49@",
  "alloc50-59@",
  "alloc60-69@",
  "alloc70-79@",
  "alloc80-89@",
  "alloc90-99@",
  "alloc_large@",
};
uintnat caml_instr_alloc_jump = 0;
/* number of pointers followed to allocate from the free list */
#endif /*CAML_INSTR*/

/**************************************************************************/
/* splay tree submodule */

#ifdef DEBUG
static mlsize_t check_cur_size = 0;
static void check_subtree (large_free_block *p)
{
  mlsize_t wosz;
  large_free_block *cur, *next;

  if (p == NULL) return;

  wosz = Wosize_val ((value) p);
  CAMLassert (p->isnode);
  check_subtree (p->left);
  CAMLassert (wosz > NUM_SMALL);
  CAMLassert (wosz > check_cur_size);
  check_cur_size = wosz;
  cur = p;
  while (1){
    CAMLassert (Wosize_val ((value) cur) == wosz);
    CAMLassert (Color_val ((value) cur) == Caml_blue);
    CAMLassert (cur == p || ! cur->isnode);
    next = cur->next;
    CAMLassert (next->prev = cur);
    if (next == p) break;
    cur = next;
  }
  check_subtree (p->right);
}
static void DEBUG_check (void)
{
  mlsize_t i;
  /* check free lists */
  for (i = 1; i <= NUM_SMALL; i++){
    value b;
    int col = 0;
    int merge_found = 0;

    if (small_fl[i].merge == &small_fl[i].free) merge_found = 1;
    for (b = small_fl[i].free; b != Val_NULL; b = Next_small (b)){
      if (small_fl[i].merge == &Next_small (b)) merge_found = 1;
      CAMLassert (Wosize_val (b) == i);
      if (Color_val (b) == Caml_blue){
        col = 1;
        CAMLassert (Next_small (b) == Val_NULL || Next_small (b) > b);
      }else{
        CAMLassert (col == 0);
        CAMLassert (Color_val (b) != Caml_gray);
      }
    }
    CAMLassert (merge_found);
  }
  /* check the tree */
  check_cur_size = 0;
  check_subtree (large_fl);
}
#else
#define DEBUG_check() ((void)0)
#endif

/* auxiliary function for find_best_fit_and_splay
   remove a block from the linked list at node x and return it
   if x is the sole element of the list, it is returned
*/
static large_free_block *remove_block (large_free_block *x)
{
  large_free_block *y = x->next;  /* head of list */
  CAMLassert (Color_val ((value) y) == Caml_blue);
  CAMLassert (Wosize_val ((value) y) > NUM_SMALL);
  CAMLassert (y == x || ! y->isnode);
  DEBUG_check ();
  x->next = y->next;
  y->next->prev = x;
  DEBUG_check ();
  return y;
}

/* Find the smallest block that is at least as large as wo_sz,
   remove it from the tree, and return it.

   We use top-down simple splaying.
   When we found a suitable block, there are two cases:
   - the list has more than 1 element, we remove it from the list
   - the list contains only the node, we must remove it from the tree
*/
static large_free_block *find_best_fit_and_splay (mlsize_t wo_sz)
{
  large_free_block *x = large_fl;
  large_free_block *y;
  large_free_block **best = NULL;
  large_free_block *left_top = NULL;
  large_free_block *right_top = NULL;
  large_free_block **left_bottom = &left_top;
  large_free_block **right_bottom = &right_top;
  large_free_block *result;

  if (large_fl == NULL) return NULL;  /* tree is empty */

  DEBUG_check ();
  while (1){
    if (Wosize_val ((value) x) == wo_sz){
      result = remove_block (x);
      if (result == x){
        /* remove x and join its two subtrees */
        large_free_block *l = x->left;
        large_free_block *r = x->right;
        if (l == NULL){
          x = r;
        }else{
          if (r != NULL){
            while (l->right != NULL) l = l->right;
            l->right = r;
          }
          x = l;
        }
      }
      break;
    }else if (Wosize_val ((value) x) > wo_sz){
      /* zig */
      if (x->left == NULL){
        result = remove_block (x);
        if (result == x) x = x->right; /* remove x and replace by its child */
        break;
      }else if (Wosize_val ((value) x->left) > wo_sz){
        /* zig-zig: rotate right */
        y = x->left;
        x->left = y->right;
        y->right = x;
        x = y;
        if (x->left == NULL){
          result = remove_block (x);
          if (result == x) x = x->right; /* remove x and replace by its child */
          break;
        }
      }
      /* link right */
      *right_bottom = x;
      best = right_bottom;
      right_bottom = &(x->left);
      x = x->left;
    }else{
      CAMLassert (Wosize_val ((value) x) < wo_sz);
      /* zag */
      if (x->right == NULL){
        if (best == NULL){
          result = NULL;
        }else{
          result = remove_block (*best);
          if (result == *best) *best = (*best)->right;
        }
        break;
      }else if (Wosize_val ((value) x->right) < wo_sz){
        /* zag-zag : rotate left */
        y = x->right;
        x->right = y->left;
        y->left = x;
        x = y;
        if (x->right == NULL){
          if (best == NULL){
            result = NULL;
          }else{
            result = remove_block (*best);
            if (result == *best) *best = (*best)->right;
          }
          break;
        }
      }
      /* link left */
      *left_bottom = x;
      left_bottom = &(x->right);
      x = x->right;
    }
  }
  if (x == NULL){
    /* The central subree has vanished; reassemble the left and right parts */
    *left_bottom = right_top;
    *right_bottom = NULL;
    large_fl = left_top;
  }else{
    /* reassemble the tree normally */
    *left_bottom = x->left;
    *right_bottom = x->right;
    x->left = left_top;
    x->right = right_top;
    large_fl = x;
  }

#ifdef DEBUG
  if (result == NULL){
    DEBUG_check ();
  }else{
    CAMLassert (Color_val ((value) result) == Caml_blue);
    Hd_val ((value) result) = Whitehd_hd (Hd_val ((value) result));
    DEBUG_check ();
    Hd_val ((value) result) = Bluehd_hd (Hd_val ((value) result));
  }
#endif
  return result;
}

/* Splay the tree at wosz, which must be found in the tree. */
static void splay (mlsize_t wosz)
{
  /* TODO */
}

/* Insert b in the tree:
   - if there is already a node of this size, insert at the tail of its
     free list and splay the tree at this node
   - otherwise, add a node to the tree and don't splay
*/
static void insert_may_splay (large_free_block *b)
{
  mlsize_t wosz = Wosize_val ((value) b);
  large_free_block **xp = &large_fl;
  large_free_block *x = large_fl;

  CAMLassert (Wosize_val ((value) b) > NUM_SMALL);
  CAMLassert (Color_val ((value) b) == Caml_blue);
  DEBUG_check ();
  while (1){
    if (x == NULL){
      b->isnode = 1;
      b->left = NULL;
      b->right = NULL;
      b->next = b;
      b->prev = b;
      *xp = b;
      break;
    }else if (Wosize_val ((value) x) == wosz){
      CAMLassert (x->isnode);
      b->isnode = 0;
      b->prev = x->prev;
      b->next = x;
      x->prev->next = b;
      x->prev = b;
      splay (wosz);
      break;
    }else if (Wosize_val ((value) x) < wosz){
      xp = &(x->right);
      x = x->right;
    }else{
      CAMLassert (Wosize_val ((value) x) > wosz);
      xp = &(x->left);
      x = x->left;
    }
  }
  DEBUG_check ();
}

/**************************************************************************/

/* Add back a fragment into the free list. The block must be black
   and its tag must be abstract. */
static void fl_insert_fragment (value v)
{
  mlsize_t wosz = Wosize_val (v);

  CAMLassert (Color_val (v) == Caml_black);
  CAMLassert (Tag_val (v) == Abstract_tag);
  if (wosz <= NUM_SMALL){
    Next_small (v) = small_fl[wosz].free;
    small_fl[wosz].free = v;
    if (small_fl[wosz].merge == &small_fl[wosz].free){
      small_fl[wosz].merge = &Next_small (v);
    }
  }else{
    Hd_val (v) = Bluehd_hd (Hd_val (v));
    insert_may_splay ((large_free_block *) v);
  }
}

/* Insert the block into the free list during sweep. The block must be blue. */
static void fl_insert_sweep (value v)
{
  mlsize_t wosz = Wosize_val (v);

  CAMLassert (Color_val (v) == Caml_blue);
  if (wosz <= NUM_SMALL){
    while (*small_fl[wosz].merge != Val_NULL && *small_fl[wosz].merge < v){
      small_fl[wosz].merge = &Next_small (*small_fl[wosz].merge);
    }
    Next_small (v) = *small_fl[wosz].merge;
    *small_fl[wosz].merge = v;
    small_fl[wosz].merge = &Next_small (v);
  }else{
    insert_may_splay ((large_free_block *) v);
  }
}

static void fl_remove (value v)
{
  mlsize_t wosz = Wosize_val (v);

  CAMLassert (Color_val (v) == Caml_blue);
  if (wosz <= NUM_SMALL){
    while (*small_fl[wosz].merge != v){
      CAMLassert (*small_fl[wosz].merge < v);
      small_fl[wosz].merge = &Next_small (*small_fl[wosz].merge);
    }
    *small_fl[wosz].merge = Next_small (v);
  }else{
    large_free_block *b = (large_free_block *) v;
    if (b->isnode){
      /* TODO remove node from list or tree */
      CAMLassert (0);
    }else{
      b->prev->next = b->next;
      b->next->prev = b->prev;
    }
  }
}

/* Split the given block, return the appropriate part and push the
   remaining part on the appropriate free list.
*/
static header_t *split_and_allocate_small (mlsize_t wo_sz, value block,
                                           mlsize_t block_wosz)
{
  mlsize_t whsz = wo_sz + 1; /* assumes header size is 1 word */
  value newblock = (value) &Field (block, whsz);
  value newsz = block_wosz - whsz;
  Hd_val (newblock) = Make_header (newsz, Abstract_tag, Caml_black);
  fl_insert_fragment (newblock);
  return Hp_val (block);
}

/* [caml_fl_allocate] does not set the header of the newly allocated block.
   The calling function must do it before any GC function gets called.
   [caml_fl_allocate] returns a head pointer, or NULL if no suitable block
   is found in the free list.
*/
header_t *caml_fl_allocate (mlsize_t wo_sz)
{
  value block;

  CAMLassert (sizeof (char *) == sizeof (value));
  CAMLassert (wo_sz >= 1);

#ifdef CAML_INSTR
  if (wo_sz < 10){
    ++instr_size[wo_sz];
  }else if (wo_sz < 100){
    ++instr_size[wo_sz/10 + 9];
  }else{
    ++instr_size[19];
  }
#endif /* CAML_INSTR */

  if (wo_sz <= NUM_SMALL){
    if (small_fl[wo_sz].free != Val_NULL){
      /* fast path: allocate from the corresponding free list */
      block = small_fl[wo_sz].free;
      if (small_fl[wo_sz].merge == &Next_small (small_fl[wo_sz].free)){
        small_fl[wo_sz].merge = &small_fl[wo_sz].free;
      }
      small_fl[wo_sz].free = Next_small (small_fl[wo_sz].free);
      return Hp_val (block);
    }else{
      /* allocate from a multiple of the size (with header) */
      mlsize_t i, s;
      i = 2;
      for (;;){
        s = (wo_sz + 1) * i - 1;  /* assumes header size is 1 word */
        if (s > NUM_SMALL) break;
        if ((block = small_fl[s].free) != Val_NULL){
          if (small_fl[s].merge == &Next_small (small_fl[s].free)){
            small_fl[s].merge = &small_fl[s].free;
          }
          small_fl[s].free = Next_small (small_fl[s].free);
          return split_and_allocate_small (wo_sz, block, s);
        }
        ++i;
      }
      /* failed to find a suitable small block: fall through and allocate
         from the tree. */
    }
  }

  {
    /* allocate from the tree of large blocks */
    /* TODO specialize find-best to find_smallest */
    value vb = (value) find_best_fit_and_splay (wo_sz);
    mlsize_t block_wosize;

    if (vb == Val_NULL) return NULL;

    block_wosize = Wosize_val (vb);

    switch (block_wosize - wo_sz){
    case 0:
      return Hp_val (vb);
    case 1:
      Hd_val (vb) = Make_header (0, 0, Caml_white);
      return (header_t *) vb;
    default:
      /* split the block and push the remainder back to the free list */
      {
        mlsize_t wh_sz = Whsize_wosize (wo_sz);
        value rem = (value) &Field (vb, Whsize_wosize (wo_sz));
        Hd_val (rem) =
          Make_header (block_wosize - wh_sz, Abstract_tag, Caml_black);
        fl_insert_fragment (rem);
        return Hp_val (vb);
      }
    }
  }
}

void caml_fl_init_merge (void)
{
  mlsize_t i;

#ifdef CAML_INSTR
  for (i = 1; i < 20; i++){
    CAML_INSTR_INT (instr_name[i], instr_size[i]);
    instr_size[i] = 0;
  }
#endif /* CAML_INSTR */

  caml_fl_merge = Val_NULL;

  for (i = 1; i <= NUM_SMALL; i++){
    /* At the beginning of each small free list is a segment of fragments
       that were pushed back to the list after splitting. These are either
       black or white, and they are not in order. We need to remove them
       from the list for coalescing to work. We set them white so they
       will be picked up by the sweeping code and inserted in the right
       place in the list.
    */
    value p = small_fl[i].free;
    while (p != Val_NULL && Color_val (p) != Caml_blue){
      CAMLassert (Color_val (p) == Caml_white || Color_val (p) == Caml_black);
      Hd_val(p) = Whitehd_hd (Hd_val (p));
      p = Next_small (p);
    }
    small_fl[i].free = p;
    /* Set the merge pointer to its initial value */
    small_fl[i].merge = &small_fl[i].free;
  }

  DEBUG_check ();
}

/* This is called by caml_compact_heap. */
void caml_fl_reset (void)
{
  /* TODO */
  CAMLassert (0);
}

#define Next(v) ((value) &Field ((v), Whsize_val (v)))

/* [caml_fl_merge_block] returns the head pointer of the next block after [bp],
   because merging blocks may change the size of [bp]. */
header_t *caml_fl_merge_block (value bp, char *limit)
{
  value start;
  value next;
  mlsize_t wosz;

  CAMLassert (Color_val (bp) == Caml_white);
  /* Find the starting point of the current run of free blocks. */
  if (caml_fl_merge != Val_NULL && Next (caml_fl_merge) == bp){
    start = caml_fl_merge;
    next = bp;
    CAMLassert (Color_val (start) == Caml_blue);
    fl_remove (start);
  }else{
    start = bp;
    next = Next (bp);
  }
  while ((char *) next <= limit){
    switch (Color_val (next)){
    case Caml_white:
      next = Next (next);
      break;
    case Caml_blue:
      fl_remove (next);
      next = Next (next);
      break;
    case Caml_gray: case Caml_black:
      goto end_while;
    }
  }
 end_while:
  wosz = Wosize_whsize ((value *) next - (value *) start);
  while (wosz > Max_wosize){
    /* TODO: cut the block into pieces of size Max_wosz */
    CAMLassert (0);
  }
  if (wosz > 1){
    Hd_val (start) = Make_header (wosz, 0, Caml_blue);
#ifdef DEBUG
    {
      mlsize_t i;
      for (i = 0; i < wosz; i++) Field (start, i) = Debug_free_major;
    }
#endif
    fl_insert_sweep (start);
  }else{
    Hd_val (start) = Make_header (1, 0, Caml_white);
  }
  return Hp_val (next);
}

/* [bp] must point to a list of blocks chained by their field 0,
   terminated by Val_NULL, and field 1 of the first block must point to
   the last block.
   The blocks must be blue.
*/
void caml_fl_add_blocks (value bp)
{
  while (bp != Val_NULL){
    value next = Next_small (bp);
    if (Wosize_val (bp) > NUM_SMALL){
      insert_may_splay ((large_free_block *) bp);
    }else{
      Hd_val (bp) = Blackhd_hd (Hd_val (bp));
    }
    bp = next;
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
    if (do_merge){
      *(header_t *)p =
        Make_header (Wosize_whsize (sz), Abstract_tag, Caml_black);
      fl_insert_fragment (Val_hp (p));
    }else{
      *(header_t *)p = Make_header (Wosize_whsize (sz), 0, color);
    }
    size -= sz;
    p += sz;
  }
}

void caml_set_allocation_policy (uintnat p)
{
  /* TODO, for the moment the policy is always best fit. */
}
