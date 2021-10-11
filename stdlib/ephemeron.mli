(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Damien Doligez, projet Para, INRIA Rocquencourt            *)
(*                                                                        *)
(*   Copyright 1997 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(** Ephemerons and weak hash table *)

(** Ephemerons and weak hash table are useful when one wants to cache
    or memorize the computation of a function, as long as the
    arguments and the function are used, without creating memory leaks
    by continuously keeping old computation results that are not
    useful anymore because one argument or the function is freed. An
    implementation using {!Hashtbl.t} is not suitable because all
    associations would keep in memory the arguments and the result.

    Ephemerons can also be used for "adding" a field to an arbitrary
    boxed ocaml value: you can attach an information to a value
    created by an external library without memory leaks.

    Ephemerons hold some keys and one or no data. They are all boxed
    ocaml values. The keys of an ephemeron have the same behavior
    than weak pointers according to the garbage collector. In fact
    ocaml weak pointers are implemented as ephemerons without data.

    The keys and data of an ephemeron are said to be full if they
    point to a value, empty if the value have never been set, have
    been unset, or was erased by the GC. In the function that accesses
    the keys or data these two states are represented by the [option]
    type.

    The data is considered by the garbage collector alive if all the
    full keys are alive and if the ephemeron is alive. When one of the
    keys is not considered alive anymore by the GC, the data is
    emptied from the ephemeron. The data could be alive for another
    reason and in that case the GC will not free it, but the ephemeron
    will not hold the data anymore.

    The ephemerons complicate the notion of liveness of values, because
    it is not anymore an equivalence with the reachability from root
    value by usual pointers (not weak and not ephemerons). With ephemerons
    the notion of liveness is constructed by the least fixpoint of:
       A value is alive if:
        - it is a root value
        - it is reachable from alive value by usual pointers
        - it is the data of an alive ephemeron with all its full keys alive

    Notes:
    - All the types defined in this module cannot be marshaled
    using {!Stdlib.output_value} or the functions of the
    {!Marshal} module.

    Ephemerons are defined in a language agnostic way in this paper:
    B. Hayes, Ephemerons: a New Finalization Mechanism, OOPSLA'9

    @since 4.03.0
*)

module type S = sig

  (* A subset of the interface of normal hash tables *)

  type key
  type !'a t
  val create : int -> 'a t
  val clear : 'a t -> unit
  val reset : 'a t -> unit

  val copy : 'a t -> 'a t
  val add : 'a t -> key -> 'a -> unit
  val remove : 'a t -> key -> unit
  val find : 'a t -> key -> 'a
  val find_opt : 'a t -> key -> 'a option

  val find_all : 'a t -> key -> 'a list
  val replace : 'a t -> key -> 'a -> unit

  val length : 'a t -> int
  val stats : 'a t -> Hashtbl.statistics

  val add_seq : 'a t -> (key * 'a) Seq.t -> unit
  val replace_seq : 'a t -> (key * 'a) Seq.t -> unit
  val of_seq : (key * 'a) Seq.t -> 'a t

  (* Additional functions, deprecated *)

  val clean: 'a t -> unit
  (** Do nothing. For backward compatibility only *)

  val stats_alive: 'a t -> Hashtbl.statistics
  (** same as {!Hashtbl.SeededS.stats}. For backward compatibility only. *)
end
(** The output signature of the functor {!K1.Make} and {!K2.Make}.
    These hash tables are weak in the keys. If all the keys of a binding are
    alive the binding is kept, but if one of the keys of the binding
    is dead then the binding is removed.
*)

module type SeededS = sig

  (* A subset of the interface of normal hash tables *)
  type key
  type !'a t
  val create : ?random (* thwart tools/sync_stdlib_docs *) :bool ->
               int -> 'a t
  val clear : 'a t -> unit
  val reset : 'a t -> unit
  val copy : 'a t -> 'a t
  val add : 'a t -> key -> 'a -> unit
  val remove : 'a t -> key -> unit
  val find : 'a t -> key -> 'a
  val find_opt : 'a t -> key -> 'a option (** @since 4.05.0 *)

  val find_all : 'a t -> key -> 'a list
  val replace : 'a t -> key -> 'a -> unit

  val length : 'a t -> int
  val stats : 'a t -> Hashtbl.statistics

  val add_seq : 'a t -> (key * 'a) Seq.t -> unit
  val replace_seq : 'a t -> (key * 'a) Seq.t -> unit
  val of_seq : (key * 'a) Seq.t -> 'a t

  val clean: 'a t -> unit  (* XXX Deprecated *)
  (** Do nothing. For backward compatibility only *)

  val stats_alive: 'a t -> Hashtbl.statistics  (* XXX Deprecated *)
  (** same as {!Hashtbl.SeededS.stats}. For backward compatibility only. *)
end
(** The output signature of the functor {!K1.MakeSeeded} and {!K2.MakeSeeded}.
*)

module K1 : sig
  type ('k,'d) t (** an ephemeron with one key *)

  val make : 'k -> 'd -> ('k,'d) t
  (** [Ephemeron.K1.make k d] creates an ephemeron with key [k] and data [d]. *)

  val query : ('k,'d) t -> 'k -> 'd option
  (** [Ephemeron.K1.get_data eph key] returns [None] if [key] is not
      physically equal to the [eph]'s key (or [eph] is empty), and [Some x]
      (where [x] is the data) if [key] matches. *)

  module Make (H:Hashtbl.HashedType) : S with type key = H.t
  (** Functor building an implementation of a weak hash table *)

  module MakeSeeded (H:Hashtbl.SeededHashedType) : SeededS with type key = H.t
  (** Functor building an implementation of a weak hash table.
      The seed is similar to the one of {!Hashtbl.MakeSeeded}. *)

end

module K2 : sig

  type ('k1,'k2,'d) t (** an ephemeron with two keys *)

  val make : 'k1 -> 'k2 -> 'd -> ('k1, 'k2, 'd) t
  (** [Ephemeron.K2.make k1 k2 d] creates an ephemeron with keys [k1] and [k2]
      and data [d]. *)

  val query : ('k1, 'k2, 'd) t -> 'k1 -> 'k2 -> 'd option
  (** [Ephemeron.K2.get_data eph key1 key2] returns [None] if [key1] and
      [key2] are not physically equal to the [eph]'s keys (or [eph] is empty),
      and [Some x] (where [x] is the data) if the keys match. *)

  module Make
      (H1:Hashtbl.HashedType)
      (H2:Hashtbl.HashedType) :
    S with type key = H1.t * H2.t
  (** Functor building an implementation of a weak hash table *)

  module MakeSeeded
      (H1:Hashtbl.SeededHashedType)
      (H2:Hashtbl.SeededHashedType) :
    SeededS with type key = H1.t * H2.t
  (** Functor building an implementation of a weak hash table.
      The seed is similar to the one of {!Hashtbl.MakeSeeded}. *)

end

module Kn : sig

  type ('k,'d) t (** an ephemeron with an arbitrary number of keys
                      of the same type *)

  val make : 'k array -> 'd -> ('k, 'd) t
  (** Similar to {!Ephemeron.K1.create} *)

  val query : ('k, 'd) t -> 'k array -> 'd option
  (** Similar to {!Ephemeron.K1.query} *)

  module Make
      (H:Hashtbl.HashedType) :
    S with type key = H.t array
  (** Functor building an implementation of a weak hash table *)

  module MakeSeeded
      (H:Hashtbl.SeededHashedType) :
    SeededS with type key = H.t array
  (** Functor building an implementation of a weak hash table.
      The seed is similar to the one of {!Hashtbl.MakeSeeded}. *)

end
(** Emphemerons with arbitrary number of keys of the same type. *)
