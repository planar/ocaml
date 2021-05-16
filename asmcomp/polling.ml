(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                Xavier Leroy, Collège de France                         *)
(*                Damien Doligez, Inria                                   *)
(*                                                                        *)
(*   Copyright 2021 Collège de France and Inria                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Mach

module String = Misc.Stdlib.String

(* replace with starts_with when it arrives *)
let isprefix s1 s2 =
  String.length s1 <= String.length s2
  && String.sub s2 0 (String.length s1) = s1

let is_assume_suppressed_poll_fun s =
  isprefix "caml_apply" s


(* Detection of recursive handlers that are not guaranteed to poll
   at every loop iteration. *)

(* The result of the analysis is a mapping from handlers H
   (= loop heads) to Booleans b and polling decisions.

   b is true if every path starting from H goes through an Ialloc,
   Ipoll, Ireturn, Itailcall_ind or Itailcall_imm instruction.
   In this case, we say that H is "safe".
   b is also true if we decide to insert a poll at the head of H.

   (Iraise is treated like Ireturn if not handled locally, or like
    a branch to the nearest enclosing exception handler.)

   b is false, therefore, if starting from H we can loop infinitely
   without crossing an Ialloc or Ipoll instruction.
   In this case, we say that H is "unsafe".
*)

(* The analysis is a backward dataflow analysis starting from false,
   using && (Boolean "and") as the join operator,
   and with the following transfer function:

   TRANSF(Ialloc | Ipoll | Itailcall_ind | Itailcall_imm _ | Ireturn) = true
   TRANSF(all other operations, x) = x
*)

(* We modify the code during the analysis in the following way:
   As soon as we find a recursive catch with some unsafe handlers
   we mark one of them for poll insertion, then we resume the analysis
   to determine whether there are still some unsafe handlers.

   Note that this means the analysis must return true in the end because
   it will have inserted polls in all unsafe loops.
*)

type handler_status = AddPoll | Polls | MayLoop

let polled_loops_analysis funbody =
  let handlers : (int, handler_status) Hashtbl.t = Hashtbl.create 20 in
  let get_handler n =
    match Hashtbl.find_opt handlers n with
    | Some (AddPoll | Polls) -> true
    | Some (MayLoop) | None -> false
  in
  let set_handler n b =
    match Hashtbl.find_opt handlers n with
    | Some AddPoll -> ()
    | _ -> Hashtbl.replace handlers n (if b then Polls else MayLoop)
  in
  let set_add_poll n = Hashtbl.replace handlers n AddPoll in
  let get_add_poll n =
    match Hashtbl.find_opt handlers n with
    | Some AddPoll -> true
    | _ -> false
  in
  let rec before i end_ exn =
    match i.desc with
    | Iend -> end_
    | Iop (Ialloc _ | Ipoll _ | Itailcall_ind | Itailcall_imm _) -> true
    | Iop (Icall_ind | Icall_imm _) ->
        exn && before i.next end_ exn
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
        let join = before i.next end_ exn in
        List.iter
          (fun (n, h) -> set_handler n (before h join exn))
          handlers;
        before body join exn
    | Icatch (Cmm.Recursive, handlers, body) ->
        let join = before i.next end_ exn in
        let update changed (n, h) =
          if get_add_poll n then changed else begin
            let b0 = get_handler n in
            let b1 = before h join exn in
            if b1 = b0 then changed else (set_handler n b1; true)
          end
        in
        let rec loop () =
          while List.fold_left update false handlers do () done;
          match List.find_opt (fun (n, _) -> not (get_handler n)) handlers with
          | None -> ()
          | Some (n, _) -> set_add_poll n; loop ()
        in
        loop ();
        before body join exn
    | Iexit n ->
        get_handler n
    | Itrywith(body, handler) ->
        let join = before i.next end_ exn in
        before body join (before handler join exn)
    | Iraise _ ->
        exn
  in
  let _r = before funbody true true in
  assert _r;
  get_add_poll

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
    | Iop (Itailcall_imm { func }) ->
        String.Set.mem func fwd_func || is_assume_suppressed_poll_fun func
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
        let join = before i.next end_ exn in
        List.iter
          (fun (n, h) -> set_handler n (before h join exn))
          handlers;
        before body join exn
    | Icatch (Cmm.Recursive, handlers, body) ->
        let join = before i.next end_ exn in
        let update changed (n, h) =
          let b0 = get_handler n in
          let b1 = before h join exn in
          if b1 = b0 then changed else (set_handler n b1; true) in
        while List.fold_left update false handlers do () done;
        before body join exn
    | Iexit n ->
        get_handler n
    | Itrywith(body, handler) ->
        let join = before i.next end_ exn in
        before body join (before handler join exn)
    | Iraise _ ->
        exn
  in
  before funbody false false

(* Given the handlers in scope without intervening allocation,
   add polls before unguarded backwards edges,
   starting from Mach instruction [i] *)
let instr_body handler_needs_poll i =
  let add_poll n i =
    if handler_needs_poll n then
      Mach.instr_cons (Iop (Ipoll { return_label = None })) [||] [||] i
    else
      i
  in
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
                       List.map (fun (n, i0) -> (n, add_poll n (instr i0))) hdl,
                       instr body);
        next = instr i.next;
      }
    | Itrywith (body, hdl) ->
      { i with
        desc = Itrywith (instr body, instr hdl);
        next = instr i.next;
      }
    | Iend | Ireturn | Iraise _ | Iexit _ -> i
    | Iop _ -> { i with next = instr i.next }
  in
  instr i

let contains_poll instr =
  let poll = ref false in
  Mach.instr_iter
     (fun i -> match i.desc with Iop (Ipoll _) -> poll := true | _ -> ())
     instr;
  !poll

let instrument_fundecl ~future_funcnames:_ (f : Mach.fundecl) : Mach.fundecl =
  if f.fun_suppress_polls then
    f
  else
    let handler_needs_poll = polled_loops_analysis f.fun_body in
    let new_body = instr_body handler_needs_poll f.fun_body in
    let new_contains_calls = f.fun_contains_calls || contains_poll new_body in
    { f with fun_body = new_body; fun_contains_calls = new_contains_calls }

let requires_prologue_poll ~future_funcnames i =
  potentially_recursive_tailcall ~fwd_func:future_funcnames i
