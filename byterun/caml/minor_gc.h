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

#ifndef CAML_MINOR_GC_H
#define CAML_MINOR_GC_H


#include "address_class.h"

CAMLextern value *caml_young_start, *caml_young_end;
CAMLextern value *caml_young_alloc_start, *caml_young_alloc_end;
CAMLextern value *caml_young_ptr, *caml_young_limit;
CAMLextern value *caml_young_trigger;

CAMLextern value *caml_young_aging_start, *caml_young_aging_mid,
                 *caml_young_aging_end;
CAMLextern value *caml_young_aging_ptr;

extern asize_t caml_minor_heap_wsz, caml_minor_aging_wsz;
extern asize_t caml_aging_size_factor;
extern int caml_young_age_limit;
extern int caml_in_minor_collection;

CAMLextern value caml_special_promote_value;

struct caml_ref_table {
  value **base;
  value **end;
  value **threshold;
  value **ptr;
  value **limit;
  asize_t size;
  asize_t reserve;
};
CAMLextern struct caml_ref_table caml_ref_table, caml_weak_ref_table;

#define Add_to_ref_table(tbl, p)                  \
  do {                                            \
    if ((tbl).ptr >= (tbl).limit){                \
      Assert ((tbl).ptr == (tbl).limit);          \
      caml_realloc_ref_table (&(tbl));            \
    }                                             \
    *(tbl).ptr++ = (p);                           \
  } while(0)

extern void caml_set_minor_heap_size (asize_t alloc_wsz, asize_t aging_factor);
extern void caml_set_minor_age_limit (asize_t limit);
CAMLextern void caml_minor_collection_clean (void);
CAMLextern void caml_minor_collection_empty (void);
CAMLextern void caml_gc_dispatch (void);
CAMLextern void garbage_collection (void); /* def in asmrun/signals.c */
extern void caml_realloc_ref_table (struct caml_ref_table *);
extern void caml_alloc_table (struct caml_ref_table *, asize_t, asize_t);
extern void caml_oldify_one (value, value *);
extern void caml_oldify_mopup (void);
extern int caml_do_full_minor;
extern void caml_minor_do_fields (void (*)(value, value *));

#define Oldify(p) do{ \
    value __oldify__v__ = *p; \
    if (Is_block (__oldify__v__) && Is_young (__oldify__v__)){ \
      caml_oldify_one (__oldify__v__, (p)); \
    } \
  }while(0)

#endif /* CAML_MINOR_GC_H */
