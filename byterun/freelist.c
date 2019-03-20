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
#include "caml/custom.h"
#include "caml/freelist.h"
#include "caml/gc.h"
#include "caml/gc_ctrl.h"
#include "caml/memory.h"
#include "caml/major_gc.h"
#include "caml/misc.h"
#include "caml/mlvalues.h"

/* quick-fit + FIFO-ordered best fit (Wilson's nomenclature)
   We use Standish's data structure (a tree of doubly-linked lists)
   with a splay tree (Sleator & Tarjan).
*/

/* [NUM_SMALL] must be at least 4 for this code to work,
   at least 5 for good performance on typical OCaml programs.
*/
#define NUM_SMALL 32

/* A block in a small free list is a [value] (integer representing a
   pointer to the first word after the block's header). The end of the
  list is NULL.
*/
#define Val_NULL ((value) NULL)

static struct {
  value free;
  value *merge;
} small_fl [NUM_SMALL + 1];

asize_t caml_fl_cur_wsz = 0;     /* Number of words in the free set,
                                    including headers but not fragments. */
/* TODO keep up to date. */

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
#define large_wosize(n) (Wosize_val((value)(n)))

static struct large_free_block *large_tree;

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
/* number of pointers followed to allocate from the free set */
/* TODO keep up to date */

#endif /*CAML_INSTR*/

/**************************************************************************/
/* debug functions for checking the data structures */

#ifdef DEBUG
static mlsize_t check_cur_size = 0;
static void check_subtree (large_free_block *p)
{
  mlsize_t wosz;
  large_free_block *cur, *next;

  if (p == NULL) return;

  wosz = large_wosize(p);
  CAMLassert (p->isnode);
  check_subtree (p->left);
  CAMLassert (wosz > NUM_SMALL);
  CAMLassert (wosz > check_cur_size);
  check_cur_size = wosz;
  cur = p;
  while (1){
    CAMLassert (large_wosize (cur) == wosz);
    CAMLassert (Color_val ((value) cur) == Caml_blue);
    CAMLassert (cur == p || ! cur->isnode);
    next = cur->next;
    CAMLassert (next->prev == cur);
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
  check_subtree (large_tree);
}

void caml_fl_check (void)
{
  DEBUG_check ();
}

#else
#define DEBUG_check() ((void)0)
#endif

/**************************************************************************/
/* splay trees */

/* Our tree is composed of nodes. Each node is the head of a doubly-linked
   circular list of blocks, all of the same size.
*/

/* Search for the node of the given size. Return a pointer to the pointer
   to the node, or a pointer to the NULL where the node should have been
   (it can be inserted here).
*/
static large_free_block **search (mlsize_t wosz)
{
  large_free_block **p = &large_tree;
  large_free_block *cur;
  mlsize_t cursz;

  while (1){
    cur = *p;
    if (cur == NULL) break;
    cursz = large_wosize (cur);
    if (cursz == wosz){
      break;
    }else if (cursz > wosz){
      p = &(cur->left);
    }else{
      CAMLassert (cursz < wosz);
      p = &(cur->right);
    }
  }
  return p;
}

/* Search for the least node that is large enough to accomodate the given
   size. Return in [next_lower] an upper bound on the size of the
   next-lower node in the tree, or NUM_SMALL if there is no such node.
*/
static large_free_block **search_best (mlsize_t wosz, mlsize_t *next_lower)
{
  large_free_block **p = &large_tree;
  large_free_block **best = NULL;
  mlsize_t lowsz = NUM_SMALL;
  large_free_block *cur;
  mlsize_t cursz;

  while (1){
    cur = *p;
    if (cur == NULL){
      *next_lower = lowsz;
      break;
    }
    cursz = large_wosize (cur);
    if (cursz == wosz){
      best = p;
      *next_lower = wosz;
      break;
    }else if (cursz > wosz){
      best = p;
      p = &(cur->left);
    }else{
      CAMLassert (cursz < wosz);
      lowsz = cursz;
      p = &(cur->right);
    }
  }
  return best;
}

/* Splay the tree at the given size. If a node of this size exists, it will
   become the root. If not, the last visited node will be the root. This is
   either the least node larger or the greatest node smaller than the given
   size.
   We use simple top-down splaying as described in S&T 85.
*/
static void splay (mlsize_t wosz)
{
  large_free_block *x, *y;
  mlsize_t xsz;
  large_free_block *left_top = NULL;
  large_free_block *right_top = NULL;
  large_free_block **left_bottom = &left_top;
  large_free_block **right_bottom = &right_top;

  x = large_tree;
  if (x == NULL) return;
  while (1){
    xsz = large_wosize (x);
    if (xsz == wosz) break;
    if (xsz > wosz){
      /* zig */
      if (x->left == NULL) break;
      if (large_wosize (x->left) > wosz){
        /* zig-zig: rotate right */
        y = x->left;
        x->left = y->right;
        y->right = x;
        x = y;
        if (x->left == NULL) break;
      }
      /* link right */
      *right_bottom = x;
      right_bottom = &(x->left);
      x = x->left;
    }else{
      CAMLassert (xsz < wosz);
      /* zag */
      if (x->right == NULL) break;
      if (large_wosize (x->right) < wosz){
        /* zag-zag : rotate left */
        y = x->right;
        x->right = y->left;
        y->left = x;
        x = y;
        if (x->right == NULL) break;
      }
      /* link left */
      *left_bottom = x;
      left_bottom = &(x->right);
      x = x->right;
    }
  }
  /* reassemble the tree */
  *left_bottom = x->left;
  *right_bottom = x->right;
  x->left = left_top;
  x->right = right_top;
  large_tree = x;
}

/* Splay the subtree at [p] on its leftmost (least) node. After this
   operation, the root node of the subtree is the least node and it
   has no left child.
   The subtree must not be empty.
*/
static void splay_least (large_free_block **p)
{
  large_free_block *x, *y;
  large_free_block *right_top = NULL;
  large_free_block **right_bottom = &right_top;

  x = *p;
  CAMLassert (x != NULL);
  while (1){
    /* We are always in the zig case. */
    if (x->left == NULL) break;
    /* And in the zig-zig case. rotate right */
    y = x->left;
    x->left = y->right;
    y->right = x;
    x = y;
    if (x->left == NULL) break;
    /* link right */
    *right_bottom = x;
    right_bottom = &(x->left);
    x = x->left;
  }
  /* reassemble the tree */
  *right_bottom = x->right;
  x->right = right_top;
  *p = x;
}

/* Remove the node at [p], if any. */
static void remove_node (large_free_block **p)
{
  large_free_block *x;
  large_free_block *l, *r;

  x = *p;
  if (x == NULL) return;
  l = x->left;
  r = x->right;
  if (l == NULL){
    *p = r;
  }else if (r == NULL){
    *p = l;
  }else{
    splay_least (&(x->right));
    r = x->right;
    r->left = l;
    *p = r;
  }
}

/* Insert a block into the tree, either as a new node or as a block in an
   existing list.
   Splay if the list is already present.
*/
static void insert_block (large_free_block *n)
{
  large_free_block **p = search (large_wosize (n));
  large_free_block *x = *p;

  CAMLassert (Color_val ((value) n) == Caml_blue);
  CAMLassert (Wosize_val ((value) n) > NUM_SMALL);
  if (x == NULL){
    /* add new node */
    n->isnode = 1;
    n->left = n->right = NULL;
    n->prev = n->next = n;
    *p = n;
  }else{
    /* insert at tail of doubly-linked list */
    CAMLassert (x->isnode);
    n->isnode = 0;
#ifdef DEBUG
    n->left = n->right = (large_free_block *) Debug_free_unused;
#endif
    n->prev = x->prev;
    n->next = x;
    x->prev->next = n;
    x->prev = n;
    splay (large_wosize (n));
  }
}

#ifdef DEBUG
static int is_in_tree (large_free_block *b)
{
  int wosz = large_wosize (b);
  large_free_block **p = search (wosz);
  large_free_block *n = *p;
  large_free_block *cur = n;

  if (n == NULL) return 0;
  while (1){
    if (cur == b) return 1;
    cur = cur->next;
    if (cur == n) return 0;
  }
}
#endif /* DEBUG */

/**************************************************************************/

/* Add back a fragment into a small free list. The block must be small
   and black and its tag must be abstract. */
static void fl_insert_fragment_small (value v)
{
  mlsize_t wosz = Wosize_val (v);

  CAMLassert (Color_val (v) == Caml_black);
  CAMLassert (Tag_val (v) == Abstract_tag);
  CAMLassert (wosz <= NUM_SMALL);
  Next_small (v) = small_fl[wosz].free;
  small_fl[wosz].free = v;
  if (small_fl[wosz].merge == &small_fl[wosz].free){
    small_fl[wosz].merge = &Next_small (v);
  }
}

/* Add back a fragment into the free set. The block must have the
   appropriate color:
   White if it is a fragment (wosize = 0)
   Black if it is a small block (0 < wosize <= NUM_SMALL)
   Blue if it is a large block (NUM_SMALL < wosize)
*/
static void fl_insert_fragment (value v)
{
  mlsize_t wosz = Wosize_val (v);

  if (wosz == 0){
    CAMLassert (Color_val (v) == Caml_white);
  }else if (wosz <= NUM_SMALL){
    CAMLassert (Color_val (v) == Caml_black);
    fl_insert_fragment_small (v);
  }else{
    CAMLassert (Color_val (v) == Caml_blue);
    insert_block ((large_free_block *) v);
  }
}
/* Insert the block into the free set during sweep. The block must be blue. */
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
    insert_block ((large_free_block *) v);
  }
}

/* Remove a given block from the free set. */
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
    CAMLassert (is_in_tree (b));
    CAMLassert (b->prev->next == b);
    CAMLassert (b->next->prev == b);
    if (b->isnode){
      large_free_block **p = search (large_wosize (b));
      CAMLassert (*p != NULL);
      if (b->next == b){
        remove_node (p);
      }else{
        large_free_block *n = b->next;
        n->prev = b->prev;
        b->prev->next = n;
        *p = n;
        n->isnode = 1;
        n->left = b->left;
        n->right = b->right;
#ifdef DEBUG
        Field ((value) b, 0) = Debug_free_major;
        b->left = b->right = b->next = b->prev =
          (large_free_block *) Debug_free_major;
#endif
      }
    }else{
      b->prev->next = b->next;
      b->next->prev = b->prev;
    }
  }
}

/* Split the given block, return a new block of the given size.
   The remaining block is still at the same address, its size is changed
   and its color becomes black if its size is greater than 0.
*/
static header_t *split_small (mlsize_t wosz, value v)
{
  intnat remwhsz = Whsize_val (v) - Whsize_wosize (wosz);

  CAMLassert (Wosize_val (v) >= wosz);
  if (remwhsz > Whsize_wosize (0)){
    Hd_val (v) =
      Make_header (Wosize_whsize (remwhsz), Abstract_tag, Caml_black);
  }else{
    Hd_val (v) = Make_header (0, 0, Caml_white);
  }
  return (header_t *) &Field (v, Wosize_whsize (remwhsz));
}

/* Split the given block, return a new block of the given size.
   The original block is at the same address but its size is changed.
   Its color and tag are changed as appropriate for calling the
   insert_fragment* functions.
*/
static header_t *split (mlsize_t wosz, value v)
{
  header_t hd = Hd_val (v);
  mlsize_t remwhsz = Whsize_hd (hd) - Whsize_wosize (wosz);

  CAMLassert (Wosize_val (v) >= wosz);
  if (remwhsz <= Whsize_wosize (0)){
    Hd_val (v) = Make_header (0, 0, Caml_white);
  }else if (remwhsz <= Whsize_wosize (NUM_SMALL)){
    Hd_val (v) =
      Make_header (Wosize_whsize (remwhsz), Abstract_tag, Caml_black);
  }else{
    Hd_val (v) =
      Make_header (Wosize_whsize (remwhsz), Abstract_tag, Caml_blue);
  }
  return (header_t *) &Field (v, Wosize_whsize (remwhsz));
}

/* Allocate from a large block at [p]. If the node is single and the remaining
   size is greater than [bound], it stays at the same place in the tree.
*/
static header_t *alloc_from_large (mlsize_t wosz, large_free_block **p,
                                   mlsize_t bound)
{
  large_free_block *n = *p;
  large_free_block *b;
  header_t *result;

  CAMLassert (large_wosize (n) >= wosz);
  if (n->next == n){
    if (large_wosize (n) > bound + wosz + 1){
      /* TODO splay at [n]? if the remainder is larger than [wosz]? */
      return split (wosz, (value) n);
    }else{
      remove_node (p);
      result = split (wosz, (value) n);
      fl_insert_fragment ((value) n);
      return result;
    }
  }else{
    b = n->next;
    n->next = b->next;
    b->next->prev = n;
    result = split (wosz, (value) b);
    /* TODO: splay at [n] if the remainder is smaller than [wosz] */
    fl_insert_fragment ((value) b);
    return result;
  }
}

/* [caml_fl_allocate] does not set the header of the newly allocated block.
   The calling function must do it before any GC function gets called.
   [caml_fl_allocate] returns a head pointer, or NULL if no suitable block
   is found in the free set.
*/
header_t *caml_fl_allocate (mlsize_t wosz)
{
  value block;
  header_t *result;

  CAMLassert (sizeof (char *) == sizeof (value));
  CAMLassert (wosz >= 1);

#ifdef CAML_INSTR
  if (wosz < 10){
    ++instr_size[wosz];
  }else if (wosz < 100){
    ++instr_size[wosz/10 + 9];
  }else{
    ++instr_size[19];
  }
#endif /* CAML_INSTR */

  if (wosz <= NUM_SMALL){
    if (small_fl[wosz].free != Val_NULL){
      /* fast path: allocate from the corresponding free list */
      block = small_fl[wosz].free;
      if (small_fl[wosz].merge == &Next_small (small_fl[wosz].free)){
        small_fl[wosz].merge = &small_fl[wosz].free;
      }
      small_fl[wosz].free = Next_small (small_fl[wosz].free);
      return Hp_val (block);
    }else{
      /* allocate from a multiple of the size (with header) */
      mlsize_t i, s;
      i = 2;
      while (1){
        s = (wosz + 1) * i - 1;  /* assumes header size is 1 word */
        if (s > NUM_SMALL) break;
        if ((block = small_fl[s].free) != Val_NULL){
          if (small_fl[s].merge == &Next_small (small_fl[s].free)){
            small_fl[s].merge = &small_fl[s].free;
          }
          small_fl[s].free = Next_small (small_fl[s].free);
          result = split_small (wosz, block);
          fl_insert_fragment_small (block);
          return result;
        }
        ++i;
      }
    }
    /* failed to find a suitable small block: allocate from the tree. */
    if (large_tree == NULL) return NULL;
    splay_least (&large_tree);
    result = alloc_from_large (wosz, &large_tree, NUM_SMALL);
    return result;
  }else{
    /* allocate a large block */
    large_free_block **n;
    mlsize_t bound;
    n = search_best (wosz, &bound);
    if (n == NULL) return NULL;
    result = alloc_from_large (wosz, n, bound);
    return result;
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
}

/* This is called by caml_compact_heap. */
void caml_fl_reset (void)
{
  mlsize_t i;

  for (i = 1; i <= NUM_SMALL; i++){
    small_fl[i].free = Val_NULL;
    small_fl[i].merge = &(small_fl[i].free);
  }
  large_tree = NULL;
  caml_fl_cur_wsz = 0;
  caml_fl_init_merge ();
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
    CAMLassert (Color_val (start) == Caml_blue);
    fl_remove (start);
  }else{
    start = bp;
  }
  next = Next (bp);
  while ((char *) next <= limit){
    switch (Color_val (next)){
    case Caml_white:
      if (Tag_val (next) == Custom_tag){
        void (*final_fun)(value) = Custom_ops_val(next)->finalize;
        if (final_fun != NULL) final_fun(next);
      }
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
    /* TODO (32-bit): cut the block into pieces of size Max_wosz */
    CAMLassert (0);
  }
  if (wosz > 0){
#ifdef DEBUG
    mlsize_t i;
    for (i = 0; i < wosz; i++) Field (start, i) = Debug_free_major;
#endif
    Hd_val (start) = Make_header (wosz, 0, Caml_blue);
    fl_insert_sweep (start);
  }else{
    Hd_val (start) = Make_header (0, 0, Caml_white);
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
      insert_block ((large_free_block *) bp);
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
      mlsize_t wosz = Wosize_whsize (sz);
      if (wosz == 0){
        color = Caml_white;
      }else if (wosz <= NUM_SMALL){
        color = Caml_black;
      }else{
        color = Caml_blue;
      }
      *(header_t *)p = Make_header (wosz, Abstract_tag, color);
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
