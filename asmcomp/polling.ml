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

(* Memo table for recursive handlers *)
let approx_memo = (Hashtbl.create 97 : (int, approx) Hashtbl.t)
let reset_approx_memo () = Hashtbl.reset approx_memo

(* Check a sequence of instructions from [i] and return
   an approximation of its behavior, joined with the [acc] argument. *)
let rec path_approx ~fwd_funcs acc i =
  match i.desc with
  | Iifthenelse (_, i0, i1) -> branch_approx ~fwd_funcs acc [| i0; i1 |] i.next
  | Iswitch (_, acts) -> branch_approx ~fwd_funcs acc acts i.next
  | Icatch (rec_flag, handlers, body) ->
    begin match path_approx ~fwd_funcs Alloc body with
    | PRTC -> (* join PRTC acc *) PRTC
    | (Exit _ | Return) as a ->
      let add =
        match rec_flag with
        | Recursive -> fun x (n, h) -> handler_approx ~fwd_funcs n x h
        | Nonrecursive -> fun x (_, h) -> path_approx ~fwd_funcs x h
      in
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
      seq_approx ~fwd_funcs acc a2 i.next
    | Alloc -> (* join Alloc acc *) acc
    end
  | Itrywith (body, handler) ->
    seq_approx ~fwd_funcs acc
      (join (path_approx ~fwd_funcs Alloc body)
         (path_approx ~fwd_funcs Alloc handler))
      i.next
  | Ireturn -> join Return acc
  | Iop (Itailcall_ind) -> (* join PRTC acc *) PRTC
  | Iop (Itailcall_imm {func; _}) ->
    if String.Set.mem func fwd_funcs then PRTC else join Return acc
  | Iend -> join (Exit (IntSet.singleton 0)) acc
  | Iexit n -> join (Exit (IntSet.singleton n)) acc
  | Iraise _ -> join Return acc
  | Iop (Ialloc _ | Ipoll _) -> (* join Alloc acc *) acc
  | Iop _ -> path_approx ~fwd_funcs acc i.next

and branch_approx ~fwd_funcs acc branches next =
  assert (branches <> [| |]);
  let join_branch a branch = path_approx ~fwd_funcs a branch in
  seq_approx ~fwd_funcs acc (Array.fold_left join_branch Alloc branches) next

and seq_approx ~fwd_funcs acc a next =
  match a with
  | Alloc -> (* join Alloc acc *) acc
  | Exit s when IntSet.mem 0 s ->
    path_approx ~fwd_funcs (join (Exit (IntSet.remove 0 s)) acc) next
  | Exit _ -> join a acc
  | PRTC -> (* join PRTC acc *) PRTC
  | Return -> path_approx ~fwd_funcs (join Return acc) next

and handler_approx ~fwd_funcs n acc i =
  match Hashtbl.find_opt approx_memo n with
  | Some a -> join a acc
  | None ->
    let a = path_approx ~fwd_funcs Alloc i in
    Hashtbl.add approx_memo n a;
    join a acc

(* This determines whether from a given instruction we unconditionally
   allocate and this is used to avoid adding polls unnecessarily *)
let path_polls n i =
  match handler_approx ~fwd_funcs:String.Set.empty n Alloc i with
  | Alloc -> true
  | Exit s when IntSet.is_empty s -> true
  | _ -> false

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
    let f s (n, i0) = if path_polls n i0 then s else IntSet.add n s in
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

let instrument_body_with_polls i =
  reset_approx_memo ();
  Fun.protect ~finally:reset_approx_memo
    (fun () -> instr_body IntSet.empty i)

let instrument_fundecl ~future_funcnames:_ (f : Mach.fundecl) : Mach.fundecl =
  { f with fun_body = instrument_body_with_polls f.fun_body }

let requires_prologue_poll ~future_funcnames i =
  reset_approx_memo ();
  let work () =
    match path_approx ~fwd_funcs:future_funcnames Alloc i with
    | PRTC -> true
    | _ -> false
  in
  Fun.protect ~finally:reset_approx_memo work
