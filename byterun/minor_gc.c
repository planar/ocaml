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

#include <string.h>
#include "config.h"
#include "fail.h"
#include "finalise.h"
#include "gc.h"
#include "gc_ctrl.h"
#include "major_gc.h"
#include "memory.h"
#include "minor_gc.h"
#include "misc.h"
#include "mlvalues.h"
#include "roots.h"
#include "signals.h"
#include "weak.h"

/* Pointers into the minor heap.
   [caml_young_base]
       The [malloc] block that contains the heap.
   [caml_young_start] ... [caml_young_end]
       The whole range of the minor heap: all young blocks are inside
       this interval.

   There are two sub-intervals:
   [caml_young_alloc_start]...[caml_young_alloc_mid]...[caml_young_alloc_end]
       The allocation arena: newly-allocated blocks are carved from
       this interval. [caml_young_alloc_mid] is the mid-point of this
       interval.
   [caml_young_aging_start]...[caml_young_aging_mid]...[caml_young_aging_end]
       The aging area, divided in two semi-spaces, which rotate roles:
       each space goes through 4 roles in a cycle:
       - from space (during GC)
       - inactive space (between GCs)
       - to space (during GC)
       - active space (between GCs)
       They are 180 degrees out of phase: when one is From, the other
       is To, and when one is Active, the other is Inactive.
       Blocks in this interval have an additional word just before
       their header: their generation counter.

       Layout:
         caml_young_start = caml_young_alloc_start
                            caml_young_alloc_mid
                            caml_young_alloc_end = caml_young_aging_start
                                                   caml_young_aging_mid
         caml_young_end =                          caml_young_aging_end

   Pointers into these spaces:
   [caml_young_ptr], [caml_young_trigger], [caml_young_limit]
       These pointers are all inside the allocation arena.
       - [caml_young_ptr] is where the next allocation will take place.
       - [caml_young_trigger] is how far we can allocate before triggering
         [caml_gc_dispatch]. Currently, it is either [caml_young_alloc_start]
         or the mid-point of the allocation arena.
       - [caml_young_limit] is the pointer that is compared to
         [caml_young_ptr] for allocation. It is either
         [caml_young_alloc_end] if a signal is pending and we are in
         native code, or [caml_young_trigger].
   [caml_young_aging_ptr]
       This is the allocation pointer for the aging area. It is always
       within the current To/Active space.
*/

asize_t caml_minor_heap_wsz, caml_minor_aging_wsz;
static void *caml_young_base = NULL;
CAMLexport value *caml_young_start = NULL, *caml_young_end = NULL;
CAMLexport value *caml_young_alloc_start = NULL,
                 *caml_young_alloc_mid = NULL,
                 *caml_young_alloc_end = NULL;
CAMLexport value *caml_young_ptr = NULL, *caml_young_limit = NULL;
CAMLexport value *caml_young_trigger = NULL;

CAMLexport value *caml_young_aging_start = NULL,
                 *caml_young_aging_mid = NULL,
                 *caml_young_aging_end = NULL;
CAMLexport value *caml_young_aging_ptr = NULL;

/* [caml_young_aging_phase] is always 0 or 1.
   When it is 0, [caml_young_aging_start]...[caml_young_aging_mid] is the
   To or Active space. When it is 1, it is the From or Inactive space.
   [caml_young_aging_phase] changes at the beginning of each minor collection.
*/
static int caml_young_aging_phase = 0;

CAMLexport struct caml_ref_table
  caml_ref_table = { NULL, NULL, NULL, NULL, NULL, 0, 0},
  caml_weak_ref_table = { NULL, NULL, NULL, NULL, NULL, 0, 0};

int caml_in_minor_collection = 0;

#define YOUNG_BASE(g) (caml_young_start_total + (g) * caml_minor_heap_size * 2)

#ifdef DEBUG
static unsigned long minor_gc_counter = 0;
extern uintnat caml_global_event_count;  /* defined in debugger.c */
#endif /* DEBUG */

void caml_alloc_table (struct caml_ref_table *tbl, asize_t sz, asize_t rsv)
{
  value **new_table;

  tbl->size = sz;
  tbl->reserve = rsv;
  new_table = (value **) caml_stat_alloc ((tbl->size + tbl->reserve)
                                          * sizeof (value *));
  if (tbl->base != NULL) caml_stat_free (tbl->base);
  tbl->base = new_table;
  tbl->ptr = tbl->base;
  tbl->threshold = tbl->base + tbl->size;
  tbl->limit = tbl->threshold;
  tbl->end = tbl->base + tbl->size + tbl->reserve;
}

static void reset_table (struct caml_ref_table *tbl)
{
  tbl->size = 0;
  tbl->reserve = 0;
  if (tbl->base != NULL) caml_stat_free (tbl->base);
  tbl->base = tbl->ptr = tbl->threshold = tbl->limit = tbl->end = NULL;
}

/* Note: the GC is already initialized iff [caml_young_base != NULL]. */
void caml_set_minor_heap_size (asize_t alloc_wsz, int aging_wsz)
{
  value *new_heap;
  void *new_heap_base;
  asize_t full_wsz;

  if (alloc_wsz & 1) ++ alloc_wsz;
  Assert (alloc_wsz >= Minor_heap_min);
  Assert (alloc_wsz <= Minor_heap_max);
  if (aging_wsz < 3 * alloc_wsz) aging_wsz = 0;
  full_wsz = alloc_wsz + aging_wsz;

  if (caml_young_ptr != caml_young_alloc_end){
    CAML_TIMER_SETUP (tmr, "force_minor/set_minor_heap_size");
    caml_minor_collection_empty ();
    caml_young_trigger = caml_young_alloc_start + caml_minor_heap_wsz / 2;
    caml_young_limit = caml_young_trigger;
  }
  CAMLassert (caml_young_ptr == caml_young_alloc_end);
  new_heap = (value *) caml_aligned_malloc (Bsize_wsize (full_wsz),
                                            0, &new_heap_base);
  if (new_heap == NULL) caml_raise_out_of_memory();
  if (caml_page_table_add(In_young, new_heap, new_heap + fullsize) != 0)
    caml_raise_out_of_memory();

  if (caml_young_base != NULL){
    caml_page_table_remove(In_young, caml_young_start_total, caml_young_end);
    free (caml_young_base);
  }
  caml_young_base = new_heap_base;
  caml_young_start = new_heap;
  caml_young_end = new_heap + full_wsz;
  caml_young_alloc_start = caml_young_start;
  caml_young_alloc_mid = caml_young_start + alloc_wsz / 2;
  caml_young_alloc_end = caml_young_start + alloc_wsz;
  caml_young_trigger = caml_young_alloc_start;
  caml_young_limit = caml_young_trigger;
  caml_young_ptr = caml_young_alloc_end;
  caml_young_aging_start = caml_young_alloc_end;
  caml_young_aging_mid = caml_young_aging_start + aging_wsz / 2;
  caml_young_aging_end = caml_young_end;
  CAMLassert (caml_young_aging_end == caml_young_aging_start + aging_wsz);
  caml_minor_heap_wsz = alloc_wsz;

  reset_table (&caml_ref_table);
  reset_table (&caml_weak_ref_table);
}

/* Allocate space of size [wosz] and tag [tag].
   Where to allocate it, depends on [v]'s age and the [age_limit]
   variable. [v] is guaranteed to be in the minor heap.
   To do a full minor GC, set [age_limit] to 0.
*/
static value alloc_next_gen (asize_t wosz, tag_t tag, value v)
{
  if (v == caml_special_promote_value){
    /* FIXME find a way to get rid of this test. */
    return caml_alloc_shr (wosz, tag);
  }else{
    value result;
    int age = 0;
    if (v >= caml_young_aging_start){
      age = Get_age (v);
    }

    if (age >= age_limit){
      return caml_alloc_shr (wosz, tag);
    }else{
      caml_young_aging_ptr -= Whsize_wosize (wosz) + 1;
      CAMLassert (caml_young_aging_ptr >= To_space_start);
      result = Val_hp (caml_young_aging_ptr + 1);
      Hd_val (result) = Make_header (wosz, tag, Caml_white);
      return result;
    }
  }
}

static value oldify_todo_list = 0;
int caml_do_full_minor = 0;

/* Note how this computation would be nicer with a different layout of the
   intermediate heaps. */
#define Is_in_from_space(v)                                             \
  ((value *) (v) >= caml_young_start_first                              \
   || (((((value *) (v) - caml_young_start_total) / caml_minor_heap_size) & 1) \
       == (young_shift != caml_minor_heap_size)))

/* Note that the tests on the tag depend on the fact that Infix_tag,
   Forward_tag, and No_scan_tag are contiguous.
*/

void caml_oldify_one (value v, value *p)
{
  value result;
  header_t hd;
  mlsize_t sz, i;
  tag_t tag;

  CAMLassert (oldify_todo_list == 0
              || (Is_young (oldify_todo_list) && Hd_val (oldify_todo_list) == 0));
 tail_call:
  if (Is_block (v) && Is_young (v) && Is_in_from_space (v)){
    Assert ((value *) Hp_val (v) >= caml_young_ptr);
    hd = Hd_val (v);
    if (hd == 0){         /* If already forwarded */
      *p = Field (v, 0);  /*  then forward pointer is first field. */
    }else{
      tag = Tag_hd (hd);
      if (tag < Infix_tag){
        value field0;

        sz = Wosize_hd (hd);
        result = alloc_next_gen (sz, tag, v);
        *p = result;
        field0 = Field (v, 0);
        Hd_val (v) = 0;            /* Set forward flag */
        Field (v, 0) = result;     /*  and forward pointer. */
        if (sz > 1){
          Field (result, 0) = field0;
          Field (result, 1) = oldify_todo_list;    /* Add this block */
          oldify_todo_list = v;                    /*  to the "to do" list. */
        }else{
          Assert (sz == 1);
          p = &Field (result, 0);
          v = field0;
          goto tail_call;
        }
      }else if (tag >= No_scan_tag){
        sz = Wosize_hd (hd);
        result = alloc_next_gen (sz, tag, v);
        for (i = 0; i < sz; i++) Field (result, i) = Field (v, i);
        Hd_val (v) = 0;            /* Set forward flag */
        Field (v, 0) = result;     /*  and forward pointer. */
        *p = result;
      }else if (tag == Infix_tag){
        mlsize_t offset = Infix_offset_hd (hd);
        caml_oldify_one (v - offset, p);   /* Cannot recurse deeper than 1. */
        *p += offset;
      }else{
        value f = Forward_val (v);
        tag_t ft = 0;
        int vv = 1;

        Assert (tag == Forward_tag);
        if (Is_block (f)){
          if (Is_young (f)){
            vv = 1;
            ft = Tag_val (Hd_val (f) == 0 ? Field (f, 0) : f);
          }else{
            vv = Is_in_value_area(f);
            if (vv){
              ft = Tag_val (f);
            }
          }
        }
        if (!vv || ft == Forward_tag || ft == Lazy_tag || ft == Double_tag){
          /* Do not short-circuit the pointer.  Copy as a normal block. */
          Assert (Wosize_hd (hd) == 1);
          result = alloc_next_gen (1, Forward_tag, v);
          *p = result;
          Hd_val (v) = 0;             /* Set (GC) forward flag */
          Field (v, 0) = result;      /*  and forward pointer. */
          p = &Field (result, 0);
          v = f;
          goto tail_call;
        }else{
          v = f;                        /* Follow the forwarding */
          goto tail_call;               /*  then oldify. */
        }
      }
    }
  }else{
    *p = v;
  }
  CAMLassert (oldify_todo_list == 0
              || (Is_young (oldify_todo_list) && Hd_val (oldify_todo_list) == 0));
}

/* Finish the work that was put off by [caml_oldify_one].
   Note that [caml_oldify_one] itself is called by oldify_mopup, so we
   have to be careful to remove the first entry from the list before
   oldifying its fields. */
void caml_oldify_mopup (void)
{
  value v, new_v, f;
  mlsize_t i;

  CAMLassert (oldify_todo_list == 0
              || (Is_young (oldify_todo_list) && Hd_val (oldify_todo_list) == 0));

  while (oldify_todo_list != 0){
    v = oldify_todo_list;                /* Get the head. */
    Assert (Hd_val (v) == 0);            /* It must be forwarded. */
    new_v = Field (v, 0);                /* Follow forward pointer. */
    oldify_todo_list = Field (new_v, 1); /* Remove from list. */

    f = Field (new_v, 0);
    if (Is_block (f) && Is_young (f)){
      caml_oldify_one (f, &Field (new_v, 0));
    }
    for (i = 1; i < Wosize_val (new_v); i++){
      f = Field (v, i);
      if (Is_block (f) && Is_young (f)){
        caml_oldify_one (f, &Field (new_v, i));
      }else{
        Field (new_v, i) = f;
      }
    }
  }
}

#ifdef DEBUG
void check_minor_value (value v, value *p)
{
  if (Is_block (v) && Is_young (v)){
    Debug_check (Hd_val(v));
    if (Tag_val (v) < No_scan_tag) Debug_check (Field(v, 0));
  }
}
#endif

/* Do a minor collection.
   If [age_limit > 0] leave the minor heap clean but maybe not empty.
   If [age_limit == 0] leave the minor heap empty.
*/
static void clean_minor_heap (void)
{
  value **r, **q;
  uintnat prev_alloc_words;

  CAMLassert (oldify_todo_list == 0);
  if (age_limit == 0 || caml_young_ptr != caml_young_alloc_end){
    CAML_TIMER_SETUP (tmr, "minor");
    caml_gc_message (0x02, "<", 0);
    prev_alloc_words = caml_allocated_words;
    caml_in_minor_collection = 1;
    caml_young_aging_phase = 1 - caml_young_aging_phase;
    caml_young_aging_ptr = To_space_end;
    if (caml_special_promote_value != 0){
      value dummy;
      caml_oldify_one (caml_special_promote_value, &dummy);
    }
    caml_oldify_local_roots();
    CAML_TIMER_TIME (tmr, "minor/local_roots");
    for (q = r = caml_ref_table.base; r < caml_ref_table.ptr; r++){
#ifdef DEBUG
      Debug_check (**r);
#endif
      caml_oldify_one (**r, *r);
      if (Is_block (**r) && Is_young (**r)){
        *q++ = *r;
      }
    }
    caml_ref_table.ptr = q;

#ifdef DEBUG
    for (r = caml_ref_table.ptr; r < caml_ref_table.end; r++)
      *r = (value *) Debug_ref_tables;
#endif
    if (caml_ref_table.ptr < caml_ref_table.threshold){
      caml_ref_table.limit = caml_ref_table.threshold;
    }
    CAML_TIMER_TIME (tmr, "minor/ref_table");
    caml_oldify_mopup ();
    CAML_TIMER_TIME (tmr, "minor/copy");

    /* We have to add to ref_table all the pointers from
       newly-promoted blocks to the non-promoted ones. */
    if (caml_young_aging_ptr != To_space_end){
      value *p;
      asize_t sz, i;
      for (p = promoted_list; p != 0; p = Age_field (p)){
        Assert (Hd_hp (p) == 0);
        value v = Field (Val_hp (p), 0);
        tag_t t = Tag_val (v);
        if (t < No_scan_tag){
          sz = Wosize_val (v);
          for (i = 0; i < sz; ++i){
            value f = Field (v, i);
            if (Is_block (f) && Is_young (f)){
              ADD_TO_REF_TABLE (caml_ref_table, &(Field (v, i)));
            }
          }
        }
      }
    }
    if (caml_special_promote_value != 0){
      value v = Field (caml_special_promote_value, 0);
      tag_t t = Tag_val (v);
      CAMLassert (Is_young (v));
      CAMLassert (Hd_val (caml_special_promote_value) == 0);
      if (t < No_scan_tag){
        sz = Wosize_val (v);
        for (i = 0; i < sz; ++i){
          value f = Field (v, i);
          if (Is_block (f) && Is_young (f)){
            ADD_TO_REF_TABLE (caml_ref_table, &(Field (v, i)));
          }
        }
      }
      caml_special_promote_value = 0;
    }
    CAML_TIMER_TIME (tmr, "minor/update_ref_table");
    for (q = r = caml_weak_ref_table.base; r < caml_weak_ref_table.ptr; r++){
#ifdef DEBUG
      Debug_check (**r);
#endif
      if (Is_block (**r) && Is_young (**r) && Is_in_from_space (**r)){
        if (Hd_val (**r) == 0){
          **r = Field (**r, 0);
          if (Is_block (**r) && Is_young (**r)){
            CAMLassert (!Is_in_from_space (**r));
            *q++ = *r;
          }
        }else{
          **r = caml_weak_none;
        }
      }
    }
    caml_weak_ref_table.ptr = q;
#ifdef DEBUG
    for (r = caml_weak_ref_table.ptr; r < caml_weak_ref_table.end; r++)
      *r = (value *) Debug_ref_tables;
#endif
    if (caml_weak_ref_table.ptr < caml_weak_ref_table.threshold){
      caml_weak_ref_table.limit = caml_weak_ref_table.threshold;
    }
    CAML_TIMER_TIME (tmr, "minor/update_weak");
    CAMLassert (caml_young_ptr >= caml_young_alloc_start);
    caml_stat_minor_words += caml_young_alloc_end - caml_young_ptr;
    caml_young_ptr = caml_young_alloc_end;
    caml_gc_message (0x02, ">", 0);
    caml_in_minor_collection = 0;
    caml_final_transfer_young ();
    CAML_TIMER_TIME (tmr, "minor/finalized");
    caml_stat_promoted_words += caml_allocated_words - prev_alloc_words;
    ++ caml_stat_minor_collections;
    if (caml_do_full_minor){
      caml_minor_marking_counter = 0;
    }else{
      if (caml_minor_marking_counter > 0) --caml_minor_marking_counter;
    }
    caml_final_transfer_young ();
    ++ caml_stat_minor_collections;
  }

#ifdef DEBUG
  CAMLassert (oldify_todo_list == 0);
  {
    value *p;
    for (p = caml_young_alloc_start; p < caml_young_alloc_end; ++p){
      *p = Debug_free_minor;
    }
    for (p = From_space_start; p < From_space_end; ++p){
      *p = Debug_free_minor;
    }
    ++ minor_gc_counter;
    caml_minor_do_fields (check_minor_value);
  }
#endif
}

/* A normal minor collection: empties the allocation zone, adds 1 to the
   age of every minor block, promotes the ones that are over the age limit.
   Also promotes caml_special_promote_value, whatever its age might be.
*/
CAMLexport void caml_minor_collection_clean (void)
{
  todo ("set age_limit depending on available size and caml_young_age_limit");
  clean_minor_heap ();
}

/* A full minor collection: completely empties the minor heap.
*/
CAMLexport void caml_minor_collection_empty (void)
{
  age_limit = 0;
  clean_minor_heap ();
}

/* Do a minor collection or a slice of major collection, call finalisation
   functions, etc.
   Leave enough room in the minor heap to allocate at least one object.
*/
CAMLexport void caml_gc_dispatch (void)
{
  value *trigger = caml_young_trigger; /* save old value of trigger */

  CAML_TIMER_SETUP(tmr, "dispatch");
  CAML_TIMER_TIME (tmr, "overhead");

  if (trigger == caml_young_alloc_start || caml_requested_minor_gc){
    /* The minor heap is full, we must do a minor collection. */
    caml_minor_collection_clean ();
    caml_requested_minor_gc = 0;
    caml_young_trigger = caml_young_alloc_start + caml_minor_heap_wsz / 2;
    caml_young_limit = caml_young_trigger;
    CAML_TIMER_TIME (tmr, "dispatch/minor");

    caml_final_do_calls ();
    CAML_TIMER_TIME (tmr, "dispatch/finalizers");

    if (caml_young_ptr - caml_young_alloc_start < Max_young_whsize){
      /* The finalizers have filled up the minor heap, we must do
         a second minor collection. */
      caml_minor_collection_clean ();
      caml_requested_minor_gc = 0;
      caml_young_trigger = caml_young_alloc_start + caml_minor_heap_wsz / 2;
      caml_young_limit = caml_young_trigger;
      CAML_TIMER_TIME (tmr, "dispatch/finalizers_minor");
    }
  }
  if (trigger != caml_young_alloc_start || caml_requested_major_slice){
    /* The minor heap is half-full, do a major GC slice. */
    caml_major_collection_slice (0);
    caml_requested_major_slice = 0;
    caml_young_trigger = caml_young_alloc_start;
    caml_young_limit = caml_young_trigger;
    CAML_TIMER_TIME (tmr, "dispatch/major");
  }
}

/* For backward compatibility with Lablgtk: do a minor collection to
   ensure that the minor heap is empty.
*/
CAMLexport void caml_minor_collection (void)
{
  caml_minor_collection_empty ();
}

CAMLexport value caml_check_urgent_gc (value extra_root)
{
  CAMLparam1 (extra_root);
  if (caml_requested_major_slice || caml_requested_minor_gc){
    CAML_TIMER_SETUP (tmr, "force_minor/check_urgent_gc");
    caml_gc_dispatch();
  }
  CAMLreturn (extra_root);
}

void caml_realloc_ref_table (struct caml_ref_table *tbl)
{                                           Assert (tbl->ptr == tbl->limit);
                                            Assert (tbl->limit <= tbl->end);
                                      Assert (tbl->limit >= tbl->threshold);

  if (tbl->base == NULL){
    caml_alloc_table (tbl, caml_minor_heap_wsz / 8, 256);
  }else if (tbl->limit == tbl->threshold){
    CAML_TIMER_SETUP (tmr, "request_minor/realloc_ref_table");
    caml_gc_message (0x08, "ref_table threshold crossed\n", 0);
    tbl->limit = tbl->end;
    caml_request_minor_gc ();
  }else{
    asize_t sz;
    asize_t cur_ptr = tbl->ptr - tbl->base;

    caml_urge_major_slice ();
    tbl->size *= 2;
    sz = (tbl->size + tbl->reserve) * sizeof (value *);
    caml_gc_message (0x08, "Growing ref_table to %"
                           ARCH_INTNAT_PRINTF_FORMAT "dk bytes\n",
                     (intnat) sz/1024);
    tbl->base = (value **) realloc ((char *) tbl->base, sz);
    if (tbl->base == NULL){
      caml_fatal_error ("Fatal error: ref_table overflow\n");
    }
    tbl->end = tbl->base + tbl->size + tbl->reserve;
    tbl->threshold = tbl->base + tbl->size;
    tbl->ptr = tbl->base + cur_ptr;
    tbl->limit = tbl->end;
  }
}

/* Call [f] on each field of each block present in the minor heap.
   The minor heap must be clean. */
extern void caml_minor_do_fields (scanning_action f)
{
  int g;
  value *p;
  asize_t i, sz;

  for (p = caml_young_alloc_ptr;
       p < caml_young_alloc_end;
       p += Whsize_wosize (sz)){
    sz = Wosize_hp (p);
    if (Tag_hp (p) < No_scan_tag){
      for (i = 0; i < sz; ++i){
        (*f) (Field (Val_hp (p), i), &Field (Val_hp (p), i));
      }
    }
  }
  for (p = caml_young_aging_ptr + 1;
       p < To_space_end;
       p += Whsize_wosize (sz) + 1){
    sz = Wosize_hp (p);
    if (Tag_hp (p) < No_scan_tag){
      for (i = 0; i < sz; ++i){
        (*f) (Field (Val_hp (p), i), &Field (Val_hp (p), i));
      }
    }
  }
}
