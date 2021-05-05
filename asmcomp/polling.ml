(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                Sadiq Jaffer, OCaml Labs Consultancy Ltd                *)
(*                                                                        *)
(*   Copyright 2020 OCaml Labs Consultancy Ltd                            *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Mach

module String = Misc.Stdlib.String

(* Detection of recursive handlers that are not guaranteed to poll
   at every loop iteration. *)

(* The result of the analysis is a mapping from handlers H
   (= loop heads) to Booleans b.

   b is true if every path starting from H goes through an Ialloc,
   Ipoll, Ireturn, Itailcall_ind or Itailcall_imm instruction.

   (Iraise is treated like Ireturn if not handled locally, or like
    a branch to the nearest enclosing exception handler.)

   b is false, therefore, if starting from H we can loop infinitely
   without crossing an Ialloc or Ipoll instruction.
*)

(* The analysis is a backward dataflow analysis starting from false,
   using && (Boolean "and") as the join operator,
   and with the following transfer function:

   TRANSF(Ialloc | Ipoll | Itailcall_ind | Itailcall_imm _ | Ireturn) = true
   TRANSF(all other operations, x) = x
*)

let polled_loops_analysis funbody =
  let handlers : (int, bool) Hashtbl.t = Hashtbl.create 20 in
  let get_handler n =
    match Hashtbl.find_opt handlers n with Some b -> b | None -> false in
  let set_handler n b =
    Hashtbl.replace handlers n b in
  let rec before i end_ exn =
    match i.desc with
    | Iend -> end_
    | Iop (Ialloc _ | Ipoll _ | Itailcall_ind | Itailcall_imm _) -> true
    | Iop (Icall_ind | Icall_imm _) ->  (* TODO: make sure we can ignore exn *)
        before i.next end_ exn
    | Iop op ->
        if operation_can_raise op
        then exn && before i.next end_ exn
        else before i.next end_ exn
    | Ireturn -> true
    | Iifthenelse(_, ifso, ifnot) ->
        let join = before i.next end_ exn in
        before ifso join exn && before ifnot join exn
    | Iswitch(_, branches) ->
        let join = before i.next end_ exn in
        Array.for_all (fun i -> before i join exn) branches
    | Icatch (Cmm.Nonrecursive, handlers, body) ->
        List.iter
          (fun (n, h) -> set_handler n (before h end_ exn))
          handlers;
        before body end_ exn
    | Icatch (Cmm.Recursive, handlers, body) ->
        let update changed (n, h) =
          let b0 = get_handler n in
          let b1 = before h end_ exn in
          if b1 = b0 then changed else (set_handler n b1; true) in
        while List.fold_left update false handlers do () done;
        before body end_ exn
    | Iexit n ->
        get_handler n
    | Itrywith(body, handler) ->
        before body end_ (before handler end_ exn)
    | Iraise _ ->
        exn
  in
    ignore (before funbody true true);
    get_handler

(* Detection of functions that can loop via a tail-call without going
   through a poll point. *)

(* The result of the analysis is a single Boolean b.

   b is true if there exists a path from the function entry to a
   Potentially Recursive Tail Call (an Itailcall_ind or
   Itailcall_imm to a forward function) 
   that does not go through an Ialloc or Ipoll instruction.

   b is false, therefore, if the function always polls (via Ialloc or Ipoll)
   before doing a PRTC.

   To compute b, we do a backward dataflow analysis starting from
   false, using || (Boolean "or") as the join operator, and with the
   following transfer function:

   TRANSF(Ialloc | Ipoll, x) = false
   TRANSF(Itailcall_ind, x) = true
   TRANSF(Itailcall_imm f, x) = f is a forward function
   TRANSF(all other operations, x) = x
*)

let potentially_recursive_tailcall ~fwd_func funbody =
  let handlers : (int, bool) Hashtbl.t = Hashtbl.create 20 in
  let get_handler n =
    match Hashtbl.find_opt handlers n with Some b -> b | None -> false in
  let set_handler n b =
    Hashtbl.replace handlers n b in
  let rec before i end_ exn =
    match i.desc with
    | Iend -> end_
    | Iop (Ialloc _ | Ipoll _) -> false
    | Iop (Itailcall_ind) -> true
    | Iop (Itailcall_imm { func }) -> String.Set.mem func fwd_func
    | Iop op ->
        if operation_can_raise op
        then exn || before i.next end_ exn
        else before i.next end_ exn
    | Ireturn -> false
    | Iifthenelse(_, ifso, ifnot) ->
        let join = before i.next end_ exn in
        before ifso join exn || before ifnot join exn
    | Iswitch(_, branches) ->
        let join = before i.next end_ exn in
        Array.exists (fun i -> before i join exn) branches
    | Icatch (Cmm.Nonrecursive, handlers, body) ->
        List.iter
          (fun (n, h) -> set_handler n (before h end_ exn))
          handlers;
        before body end_ exn
    | Icatch (Cmm.Recursive, handlers, body) ->
        let update changed (n, h) =
          let b0 = get_handler n in
          let b1 = before h end_ exn in
          if b1 = b0 then changed else (set_handler n b1; true) in
        while List.fold_left update false handlers do () done;
        before body end_ exn
    | Iexit n ->
        get_handler n
    | Itrywith(body, handler) ->
        before body end_ (before handler end_ exn)
    | Iraise _ ->
        exn
  in
    before funbody false false

(* Given the handlers in scope without intervening allocation,
   add polls before unguarded backwards edges,
   starting from Mach instruction [i] *)
let instr_body handler_ok i =
  let rec instr i =
  match i.desc with
  | Iifthenelse (test, i0, i1) ->
    { i with
      desc = Iifthenelse (test, instr i0, instr i1);
      next = instr i.next;
    }
  | Iswitch (index, cases) ->
    { i with
      desc = Iswitch (index, Array.map instr cases);
      next = instr i.next;
    }
  | Icatch (rc, hdl, body) ->
    { i with
      desc = Icatch (rc,
                     List.map (fun (n, i0) -> (n, instr i0)) hdl,
                     instr body);
      next = instr i.next;
    }
  | Itrywith (body, hdl) ->
    { i with
      desc = Itrywith (instr body, instr hdl);
      next = instr i.next;
    }
  | Iexit n ->
    if handler_ok n then
      i
    else
      Mach.instr_cons (Iop (Ipoll { return_label = None })) [||] [||] i
  | Iend | Ireturn | Iraise _ -> i
  | Iop _ -> { i with next = instr i.next }
  in
    instr i

let instrument_fundecl ~future_funcnames:_ (f : Mach.fundecl) : Mach.fundecl =
  let handlers_ok = polled_loops_analysis f.fun_body in
  { f with fun_body = instr_body handlers_ok f.fun_body }

let requires_prologue_poll ~future_funcnames i =
  potentially_recursive_tailcall ~fwd_func:future_funcnames i
