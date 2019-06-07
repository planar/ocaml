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

/*************** declarations common to all policies ******************/

/* A block in a small free list is a [value] (integer representing a
   pointer to the first word after the block's header). The end of the
  list is NULL.
*/
#define Val_NULL ((value) NULL)

asize_t caml_fl_cur_wsz = 0;     /* Number of words in the free set,
                                    including headers but not fragments. */

value caml_fl_merge = Val_NULL;  /* Current insertion pointer.  Managed
                                    jointly with [sweep_slice]. */

/* Next in list */
#define Next_small(v) Field ((v), 0)

/* Next in memory order */
static inline value Next (value v) {
  return (value) &Field ((v), Whsize_val (v));
}

typedef enum caml_policy_t {
  policy_next_fit,
  policy_first_fit,
  policy_best_fit,
} caml_policy_t;
caml_policy_t caml_allocation_policy = policy_best_fit;
#define policy caml_allocation_policy

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

#define INSTR_alloc_jump(n) (caml_instr_alloc_jump += (n))

#else

#define INSTR_alloc_jump(n) ((void)0)

#endif /*CAML_INSTR*/


/******************** "best-fit" allocation policy ********************/

/* quick-fit + FIFO-ordered best fit (Wilson's nomenclature)
   We use Standish's data structure (a tree of doubly-linked lists)
   with a splay tree (Sleator & Tarjan).
*/

/* [BF_NUM_SMALL] must be at least 4 for this code to work
   and at least 5 for good performance on typical OCaml programs.
*/
#define BF_NUM_SMALL 16

static struct {
  value free;
  value *merge;
} bf_small_fl [BF_NUM_SMALL + 1];

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

static inline mlsize_t bf_large_wosize (struct large_free_block *n) {
  return Wosize_val((value)(n));
}

static struct large_free_block *bf_large_tree;


/* debug functions for checking the data structures */

#ifdef DEBUG
static mlsize_t bf_check_cur_size = 0;
static asize_t bf_check_subtree (large_free_block *p)
{
  mlsize_t wosz;
  large_free_block *cur, *next;
  asize_t total_size = 0;

  if (p == NULL) return 0;

  wosz = bf_large_wosize(p);
  CAMLassert (p->isnode);
  total_size += bf_check_subtree (p->left);
  CAMLassert (wosz > BF_NUM_SMALL);
  CAMLassert (wosz > bf_check_cur_size);
  bf_check_cur_size = wosz;
  cur = p;
  while (1){
    CAMLassert (bf_large_wosize (cur) == wosz);
    CAMLassert (Color_val ((value) cur) == Caml_blue);
    CAMLassert (cur == p || ! cur->isnode);
    total_size += Whsize_wosize (wosz);
    next = cur->next;
    CAMLassert (next->prev == cur);
    if (next == p) break;
    cur = next;
  }
  total_size += bf_check_subtree (p->right);
  return total_size;
}

static void bf_fl_check (void)
{
  mlsize_t i;
  asize_t total_size = 0;

  /* check free lists */
  for (i = 1; i <= BF_NUM_SMALL; i++){
    value b;
    int col = 0;
    int merge_found = 0;

    if (bf_small_fl[i].merge == &bf_small_fl[i].free) merge_found = 1;
    for (b = bf_small_fl[i].free; b != Val_NULL; b = Next_small (b)){
      if (bf_small_fl[i].merge == &Next_small (b)) merge_found = 1;
      CAMLassert (Wosize_val (b) == i);
      total_size += Whsize_wosize (i);
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
  bf_check_cur_size = 0;
  total_size += bf_check_subtree (bf_large_tree);
  /* check the total free set size */
  CAMLassert (total_size == caml_fl_cur_wsz);
}

#define DEBUG_bf_check() bf_fl_check()

#else
#define DEBUG_bf_check() ((void)0)
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
static large_free_block **bf_search (mlsize_t wosz)
{
  large_free_block **p = &bf_large_tree;
  large_free_block *cur;
  mlsize_t cursz;

  while (1){
    cur = *p;
    INSTR_alloc_jump (1);
    if (cur == NULL) break;
    cursz = bf_large_wosize (cur);
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
   next-lower node in the tree, or BF_NUM_SMALL if there is no such node.
*/
static large_free_block **bf_search_best (mlsize_t wosz, mlsize_t *next_lower)
{
  large_free_block **p = &bf_large_tree;
  large_free_block **best = NULL;
  mlsize_t lowsz = BF_NUM_SMALL;
  large_free_block *cur;
  mlsize_t cursz;

  while (1){
    cur = *p;
    INSTR_alloc_jump (1);
    if (cur == NULL){
      *next_lower = lowsz;
      break;
    }
    cursz = bf_large_wosize (cur);
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
static void bf_splay (mlsize_t wosz)
{
  large_free_block *x, *y;
  mlsize_t xsz;
  large_free_block *left_top = NULL;
  large_free_block *right_top = NULL;
  large_free_block **left_bottom = &left_top;
  large_free_block **right_bottom = &right_top;

  x = bf_large_tree;
  if (x == NULL) return;
  while (1){
    xsz = bf_large_wosize (x);
    if (xsz == wosz) break;
    if (xsz > wosz){
      /* zig */
      y = x->left;
      INSTR_alloc_jump (1);
      if (y == NULL) break;
      if (bf_large_wosize (y) > wosz){
        /* zig-zig: rotate right */
        x->left = y->right;
        y->right = x;
        x = y;
        y = x->left;
        INSTR_alloc_jump (2);
        if (y == NULL) break;
      }
      /* link right */
      *right_bottom = x;
      right_bottom = &(x->left);
      x = y;
    }else{
      CAMLassert (xsz < wosz);
      /* zag */
      y = x->right;
      INSTR_alloc_jump (1);
      if (y == NULL) break;
      if (bf_large_wosize (y) < wosz){
        /* zag-zag : rotate left */
        x->right = y->left;
        y->left = x;
        x = y;
        y = x->right;
        INSTR_alloc_jump (2);
        if (y == NULL) break;
      }
      /* link left */
      *left_bottom = x;
      left_bottom = &(x->right);
      x = y;
    }
  }
  /* reassemble the tree */
  *left_bottom = x->left;
  *right_bottom = x->right;
  x->left = left_top;
  x->right = right_top;
  INSTR_alloc_jump (2);
  bf_large_tree = x;
}

/* Splay the subtree at [p] on its leftmost (least) node. After this
   operation, the root node of the subtree is the least node and it
   has no left child.
   The subtree must not be empty.
*/
static void bf_splay_least (large_free_block **p)
{
  large_free_block *x, *y;
  large_free_block *right_top = NULL;
  large_free_block **right_bottom = &right_top;

  x = *p;
  INSTR_alloc_jump (1);
  CAMLassert (x != NULL);
  while (1){
    /* We are always in the zig case. */
    y = x->left;
    INSTR_alloc_jump (1);
    if (y == NULL) break;
    /* And in the zig-zig case. rotate right */
    x->left = y->right;
    y->right = x;
    x = y;
    y = x->left;
    INSTR_alloc_jump (2);
    if (y == NULL) break;
    /* link right */
    *right_bottom = x;
    right_bottom = &(x->left);
    x = y;
  }
  /* reassemble the tree */
  *right_bottom = x->right;
  INSTR_alloc_jump (1);
  x->right = right_top;
  *p = x;
}

/* Remove the node at [p], if any. */
static void bf_remove_node (large_free_block **p)
{
  large_free_block *x;
  large_free_block *l, *r;

  x = *p;
  INSTR_alloc_jump (1);
  if (x == NULL) return;
  l = x->left;
  r = x->right;
  INSTR_alloc_jump (2);
  if (l == NULL){
    *p = r;
  }else if (r == NULL){
    *p = l;
  }else{
    bf_splay_least (&(x->right));
    r = x->right;
    INSTR_alloc_jump (1);
    r->left = l;
    *p = r;
  }
}

/* Insert a block into the tree, either as a new node or as a block in an
   existing list.
   Splay if the list is already present.
*/
static void bf_insert_block (large_free_block *n)
{
  large_free_block **p = bf_search (bf_large_wosize (n));
  large_free_block *x = *p;
  INSTR_alloc_jump (1);

  CAMLassert (Color_val ((value) n) == Caml_blue);
  CAMLassert (Wosize_val ((value) n) > BF_NUM_SMALL);
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
    INSTR_alloc_jump (2);
    bf_splay (bf_large_wosize (n));
  }
}

#ifdef DEBUG
static int bf_is_in_tree (large_free_block *b)
{
  int wosz = bf_large_wosize (b);
  large_free_block **p = bf_search (wosz);
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
static void bf_insert_fragment_small (value v)
{
  mlsize_t wosz = Wosize_val (v);

  CAMLassert (Color_val (v) == Caml_black);
  CAMLassert (Tag_val (v) == Abstract_tag);
  CAMLassert (1 <= wosz && wosz <= BF_NUM_SMALL);
  Next_small (v) = bf_small_fl[wosz].free;
  bf_small_fl[wosz].free = v;
  if (bf_small_fl[wosz].merge == &bf_small_fl[wosz].free){
    bf_small_fl[wosz].merge = &Next_small (v);
  }
}

/* Add back a fragment into the free set. The block must have the
   appropriate color:
   White if it is a fragment (wosize = 0)
   Black if it is a small block (0 < wosize <= BF_NUM_SMALL)
   Blue if it is a large block (BF_NUM_SMALL < wosize)
*/
static void bf_insert_fragment (value v)
{
  mlsize_t wosz = Wosize_val (v);

  if (wosz == 0){
    CAMLassert (Color_val (v) == Caml_white);
  }else if (wosz <= BF_NUM_SMALL){
    CAMLassert (Color_val (v) == Caml_black);
    bf_insert_fragment_small (v);
  }else{
    CAMLassert (Color_val (v) == Caml_blue);
    bf_insert_block ((large_free_block *) v);
  }
}
/* Insert the block into the free set during sweep. The block must be blue. */
static void bf_insert_sweep (value v)
{
  mlsize_t wosz = Wosize_val (v);
  value next;

  CAMLassert (Color_val (v) == Caml_blue);
  if (wosz <= BF_NUM_SMALL){
    while (1){
      next = *bf_small_fl[wosz].merge;
      if (next == Val_NULL || next >= v) break;
      bf_small_fl[wosz].merge = &Next_small (next);
    }
    Next_small (v) = *bf_small_fl[wosz].merge;
    *bf_small_fl[wosz].merge = v;
    bf_small_fl[wosz].merge = &Next_small (v);
  }else{
    bf_insert_block ((large_free_block *) v);
  }
}

/* Remove a given block from the free set. */
static void bf_remove (value v)
{
  mlsize_t wosz = Wosize_val (v);

  CAMLassert (Color_val (v) == Caml_blue);
  if (wosz <= BF_NUM_SMALL){
    while (*bf_small_fl[wosz].merge != v){
      CAMLassert (*bf_small_fl[wosz].merge < v);
      bf_small_fl[wosz].merge = &Next_small (*bf_small_fl[wosz].merge);
    }
    *bf_small_fl[wosz].merge = Next_small (v);
  }else{
    large_free_block *b = (large_free_block *) v;
    CAMLassert (bf_is_in_tree (b));
    CAMLassert (b->prev->next == b);
    CAMLassert (b->next->prev == b);
    if (b->isnode){
      large_free_block **p = bf_search (bf_large_wosize (b));
      CAMLassert (*p != NULL);
      if (b->next == b){
        bf_remove_node (p);
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
static header_t *bf_split_small (mlsize_t wosz, value v)
{
  intnat remwhsz = Whsize_val (v) - Whsize_wosize (wosz);

  CAMLassert (Wosize_val (v) >= wosz);
  if (remwhsz > Whsize_wosize (0)){
    Hd_val (v) =
      Make_header (Wosize_whsize (remwhsz), Abstract_tag, Caml_black);
    caml_fl_cur_wsz -= Whsize_wosize (wosz);
  }else{
    Hd_val (v) = Make_header (0, 0, Caml_white);
    caml_fl_cur_wsz -= Whsize_val (v);
  }
  return (header_t *) &Field (v, Wosize_whsize (remwhsz));
}

/* Split the given block, return a new block of the given size.
   The original block is at the same address but its size is changed.
   Its color and tag are changed as appropriate for calling the
   insert_fragment* functions.
*/
static header_t *bf_split (mlsize_t wosz, value v)
{
  header_t hd = Hd_val (v);
  mlsize_t remwhsz = Whsize_hd (hd) - Whsize_wosize (wosz);

  CAMLassert (Wosize_val (v) >= wosz);
  if (remwhsz <= Whsize_wosize (0)){
    Hd_val (v) = Make_header (0, 0, Caml_white);
    caml_fl_cur_wsz -= Whsize_hd (hd);
  }else if (remwhsz <= Whsize_wosize (BF_NUM_SMALL)){
    Hd_val (v) =
      Make_header (Wosize_whsize (remwhsz), Abstract_tag, Caml_black);
    caml_fl_cur_wsz -= Whsize_wosize (wosz);
  }else{
    Hd_val (v) =
      Make_header (Wosize_whsize (remwhsz), Abstract_tag, Caml_blue);
    caml_fl_cur_wsz -= Whsize_wosize (wosz);
  }
  return (header_t *) &Field (v, Wosize_whsize (remwhsz));
}

/* Allocate from a large block at [p]. If the node is single and the remaining
   size is greater than [bound], it stays at the same place in the tree.
*/
static header_t *bf_alloc_from_large (mlsize_t wosz, large_free_block **p,
                                      mlsize_t bound)
{
  large_free_block *n = *p;
  large_free_block *b;
  header_t *result;

  CAMLassert (bf_large_wosize (n) >= wosz);
  if (n->next == n){
    if (bf_large_wosize (n) > bound + wosz + 1){
      /* TODO splay at [n]? if the remainder is larger than [wosz]? */
      return bf_split (wosz, (value) n);
    }else{
      bf_remove_node (p);
      result = bf_split (wosz, (value) n);
      bf_insert_fragment ((value) n);
      return result;
    }
  }else{
    b = n->next;
    n->next = b->next;
    b->next->prev = n;
    result = bf_split (wosz, (value) b);
    /* TODO: splay at [n] if the remainder is smaller than [wosz] */
    bf_insert_fragment ((value) b);
    return result;
  }
}

static header_t *bf_allocate (mlsize_t wosz)
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

  DEBUG_bf_check ();
  if (wosz <= BF_NUM_SMALL){
    if (bf_small_fl[wosz].free != Val_NULL){
      /* fast path: allocate from the corresponding free list */
      block = bf_small_fl[wosz].free;
      if (bf_small_fl[wosz].merge == &Next_small (bf_small_fl[wosz].free)){
        bf_small_fl[wosz].merge = &bf_small_fl[wosz].free;
      }
      bf_small_fl[wosz].free = Next_small (bf_small_fl[wosz].free);
      caml_fl_cur_wsz -= Whsize_wosize (wosz);
  DEBUG_bf_check ();
      return Hp_val (block);
    }else{
      /* allocate from the next available size */
      mlsize_t s = wosz + 1;
      while (1){
        if (s > BF_NUM_SMALL) break;
        if ((block = bf_small_fl[s].free) != Val_NULL){
          if (bf_small_fl[s].merge == &Next_small (bf_small_fl[s].free)){
            bf_small_fl[s].merge = &bf_small_fl[s].free;
          }
          bf_small_fl[s].free = Next_small (bf_small_fl[s].free);
          result = bf_split_small (wosz, block);
          if (s - wosz > 1) bf_insert_fragment_small (block);
          return result;
        }
        ++s;
      }
    }
    /* failed to find a suitable small block: allocate from the tree. */
    if (bf_large_tree == NULL) return NULL;
    bf_splay_least (&bf_large_tree);
    result = bf_alloc_from_large (wosz, &bf_large_tree, BF_NUM_SMALL);
  DEBUG_bf_check ();
    return result;
  }else{
    /* allocate a large block */
    large_free_block **n;
    mlsize_t bound;
    n = bf_search_best (wosz, &bound);
    if (n == NULL) return NULL;
    result = bf_alloc_from_large (wosz, n, bound);
  DEBUG_bf_check ();
    return result;
  }
}

static void bf_init_merge (void)
{
  mlsize_t i;

#ifdef CAML_INSTR
  for (i = 1; i < 20; i++){
    CAML_INSTR_INT (instr_name[i], instr_size[i]);
    instr_size[i] = 0;
  }
#endif /* CAML_INSTR */

  caml_fl_merge = Val_NULL;

  for (i = 1; i <= BF_NUM_SMALL; i++){
    /* At the beginning of each small free list is a segment of fragments
       that were pushed back to the list after splitting. These are either
       black or white, and they are not in order. We need to remove them
       from the list for coalescing to work. We set them white so they
       will be picked up by the sweeping code and inserted in the right
       place in the list.
    */
    value p = bf_small_fl[i].free;
    while (p != Val_NULL && Color_val (p) != Caml_blue){
      CAMLassert (Color_val (p) == Caml_white || Color_val (p) == Caml_black);
      Hd_val(p) = Whitehd_hd (Hd_val (p));
      caml_fl_cur_wsz -= Whsize_val (p);
      p = Next_small (p);
    }
    bf_small_fl[i].free = p;
    /* Set the merge pointer to its initial value */
    bf_small_fl[i].merge = &bf_small_fl[i].free;
  }
}

static void bf_reset (void)
{
  mlsize_t i;

  for (i = 1; i <= BF_NUM_SMALL; i++){
    bf_small_fl[i].free = Val_NULL;
    bf_small_fl[i].merge = &(bf_small_fl[i].free);
  }
  bf_large_tree = NULL;
  caml_fl_cur_wsz = 0;
  bf_init_merge ();
}

static header_t *bf_merge_block (value bp, char *limit)
{
  value start;
  value next;
  mlsize_t wosz;

  DEBUG_bf_check ();
  CAMLassert (Color_val (bp) == Caml_white);
  caml_fl_cur_wsz += Whsize_val (bp);
  /* Find the starting point of the current run of free blocks. */
  if (caml_fl_merge != Val_NULL && Next (caml_fl_merge) == bp){
    start = caml_fl_merge;
    CAMLassert (Color_val (start) == Caml_blue);
    bf_remove (start);
  }else{
    start = bp;
  }
  next = bp;
  while ((char *) next <= limit){
    switch (Color_val (next)){
    case Caml_white:
      if (Tag_val (next) == Custom_tag){
        void (*final_fun)(value) = Custom_ops_val(next)->finalize;
        if (final_fun != NULL) final_fun(next);
      }
      caml_fl_cur_wsz += Whsize_val (next);
      next = Next (next);
      break;
    case Caml_blue:
      bf_remove (next);
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
    bf_insert_sweep (start);
  }else{
    Hd_val (start) = Make_header (0, 0, Caml_white);
    caml_fl_cur_wsz -= Whsize_wosize (0);
  }
  DEBUG_bf_check ();
  return Hp_val (next);
}

static void bf_add_blocks (value bp)
{
  while (bp != Val_NULL){
    value next = Next_small (bp);
    mlsize_t wosz = Wosize_val (bp);

    caml_fl_cur_wsz += Whsize_wosize (wosz);
    if (wosz > BF_NUM_SMALL){
      bf_insert_block ((large_free_block *) bp);
    }else{
      Hd_val (bp) = Blackhd_hd (Hd_val (bp));
      bf_insert_fragment_small (bp);
    }
    bp = next;
  }
}

static void bf_make_free_blocks (value *p, mlsize_t size, int do_merge,
                                 int color)
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
      }else if (wosz <= BF_NUM_SMALL){
        caml_fl_cur_wsz += Whsize_wosize (wosz);
        color = Caml_black;
      }else{
        caml_fl_cur_wsz += Whsize_wosize (wosz);
        color = Caml_blue;
      }
      *(header_t *)p = Make_header (wosz, Abstract_tag, color);
      bf_insert_fragment (Val_hp (p));
    }else{
      *(header_t *)p = Make_header (Wosize_whsize (sz), 0, color);
    }
    size -= sz;
    p += sz;
  }
}

/********************* exported functions *****************************/

/* [caml_fl_allocate] does not set the header of the newly allocated block.
   The calling function must do it before any GC function gets called.
   [caml_fl_allocate] returns a head pointer, or NULL if no suitable block
   is found in the free set.
*/
header_t *caml_fl_allocate (mlsize_t wo_sz)
{
  return bf_allocate (wo_sz);
}

void caml_fl_init_merge (void)
{
  bf_init_merge ();
}

/* This is called by caml_compact_heap. */
void caml_fl_reset (void)
{
  bf_reset ();
}

/* [caml_fl_merge_block] returns the head pointer of the next block after [bp],
   because merging blocks may change the size of [bp]. */
header_t *caml_fl_merge_block (value bp, char *limit)
{
  return bf_merge_block (bp, limit);
}

/* [bp] must point to a list of blocks of wosize >= 1 chained by their field 0,
   terminated by Val_NULL, and field 1 of the first block must point to
   the last block.
   The blocks must be blue.
*/
void caml_fl_add_blocks (value bp)
{
  bf_add_blocks (bp);
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
  bf_make_free_blocks (p, size, do_merge, color);
}

void caml_set_allocation_policy (uintnat p)
{
  switch (p){
  case policy_next_fit:
    caml_fatal_error ("allocation policy 0 not implemented");
  case policy_first_fit:
    caml_fatal_error ("allocation policy 1 not implemented");
  case policy_best_fit:
    caml_allocation_policy = policy_best_fit;
  default:
    caml_allocation_policy = policy_best_fit;
  }
}

#ifdef DEBUG
void caml_fl_check (void)
{
  bf_fl_check ();
}
#endif
