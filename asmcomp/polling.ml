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

module IntSet = Set.Make (Int)

(* Approximation of the behavior of a block of code. *)
type approx =
  | PRTC             (** The block can do a Potentially-Recursive Tail-Call
                         without allocating *)
  | Return           (** The block can return or (non-rec) tail-call
                         or raise without allocating *)
  | Exit of IntSet.t (** The block can reach one of these exits
                         without allocating; 0 represents Iend *)
  | Alloc            (** The block allocates in all cases *)

(* Upper bound of two approximations *)
let join a1 a2 =
  match a1, a2 with
  | PRTC, _ | _, PRTC -> PRTC
  | Return, _ | _, Return -> Return
  | Exit s1, Exit s2 -> Exit (IntSet.union s1 s2)
  | (Exit _ as a), Alloc | Alloc, (Exit _ as a) -> a
  | Alloc, Alloc -> Alloc

(* Check a sequence of instructions from [i] and return
   an approximation of its behavior *)
let rec path_approx ~fwd_funcs i =
  match i.desc with
  | Iifthenelse (_, i0, i1) -> branch_approx ~fwd_funcs [| i0; i1 |] i.next
  | Iswitch (_, acts) -> branch_approx ~fwd_funcs acts i.next
  | Icatch (_, handlers, body) ->
    begin match path_approx ~fwd_funcs body with
    | PRTC -> PRTC
    | (Exit _ | Return) as a ->
      let add acc (_, h) = join acc (path_approx ~fwd_funcs h) in
      let a1 = List.fold_left add a handlers in
      let a2 =
        match a1 with
        | PRTC -> PRTC
        | Return -> Return
        | Exit s1 ->
          let remove s (n, _) = IntSet.remove n s in
          Exit (List.fold_left remove s1 handlers)
        | Alloc -> assert false
      in
      seq_approx ~fwd_funcs a2 i.next
    | Alloc -> Alloc
    end
  | Itrywith (body, handler) ->
    seq_approx ~fwd_funcs
      (join (path_approx ~fwd_funcs body) (path_approx ~fwd_funcs handler))
      i.next
  | Ireturn -> Return
  | Iop (Itailcall_ind) -> PRTC
  | Iop (Itailcall_imm {func; _}) ->
    if String.Set.mem func fwd_funcs then PRTC else Return
  | Iend -> Exit (IntSet.singleton 0)
  | Iexit n -> Exit (IntSet.singleton n)
  | Iraise _ -> Return
  | Iop (Ialloc _ | Ipoll _) -> Alloc
  | Iop _ -> path_approx ~fwd_funcs i.next

and branch_approx ~fwd_funcs branches next =
  assert (branches <> [| |]);
  let join_branch acc branch = join acc (path_approx ~fwd_funcs branch) in
  seq_approx ~fwd_funcs (Array.fold_left join_branch Alloc branches) next

and seq_approx ~fwd_funcs a next =
  match a with
  | Alloc -> Alloc
  | Exit s when IntSet.mem 0 s ->
    join (Exit (IntSet.remove 0 s)) (path_approx ~fwd_funcs next)
  | Exit _ -> a
  | PRTC -> PRTC
  | Return -> join Return (path_approx ~fwd_funcs next)

let path_polls i =
  match path_approx ~fwd_funcs:String.Set.empty i with
  | Alloc -> true
  | Exit s when IntSet.is_empty s -> true
  | _ -> false

let requires_prologue_poll ~future_funcnames i =
  match path_approx ~fwd_funcs:future_funcnames i with
  | PRTC -> true
  | _ -> false

(* This determines whether from a given instruction we unconditionally
   allocate and this is used to avoid adding polls unnecessarily *)
let polls_unconditionally (i : Mach.instruction) =
  path_polls i

(* Given the handlers in scope without intervening allocation,
   add polls before unguarded backwards edges,
   starting from Mach instruction [i] *)
let rec instr_body handlers i =
  let instr i = instr_body handlers i in
  match i.desc with
  | Iop (Ialloc _ | Ipoll _) ->
    { i with next = instr_body IntSet.empty i.next }
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
  | Icatch (Nonrecursive, hdl, body) ->
    { i with
      desc = Icatch (Nonrecursive,
                     List.map (fun (n, i0) -> (n, instr i0)) hdl,
                     instr body);
      next = instr i.next;
    }
  | Icatch (Recursive, hdl, body) ->
    let f s (n, i0) = if polls_unconditionally i0 then s else IntSet.add n s in
    let new_handlers = List.fold_left f handlers hdl in
    let instr_handler (n, i0) = (n, instr_body new_handlers i0) in
    { i with
      desc = Icatch (Recursive, List.map instr_handler hdl, instr body);
      next = instr i.next;
    }
  | Itrywith (body, hdl) ->
    { i with
      desc = Itrywith (instr body, instr hdl);
      next = instr i.next;
    }
  | Iexit n ->
    if IntSet.mem n handlers then
      Mach.instr_cons (Iop (Ipoll { return_label = None })) [||] [||] i
    else
      i
  | Iend | Ireturn | Iraise _ -> i
  | Iop _ -> { i with next = instr i.next }

let instrument_body_with_polls i = instr_body IntSet.empty i

let instrument_fundecl ~future_funcnames:_ (f : Mach.fundecl) : Mach.fundecl =
  { f with fun_body = instrument_body_with_polls f.fun_body }
