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
                         without allocating *)
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

(* Check a sequence of instructions from [f] and return
   an approximation of its behavior *)
let rec path_approx ~fwd_funcs f =
  match f.desc with
  | Iifthenelse (_, i0, i1) -> branch_approx ~fwd_funcs [| i0; i1 |] f.next
  | Iswitch (_, acts) -> branch_approx ~fwd_funcs acts f.next
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
          let remove s (i, _) = IntSet.remove i s in
          Exit (List.fold_left remove s1 handlers)
        | Alloc -> assert false
      in
      seq_approx ~fwd_funcs a2 f.next
    | Alloc -> Alloc
    end
  | Itrywith (body, _handler) ->
    (* in general, this would be:
         seq_approx ~fwd_funcs
                    (join (path_approx ~fwd_funcs body)
                          (path_approx ~fwd_funcs handler))
                    f.next
       but we insert a poll at every raise, so we can ignore the handler
       as if it allocated immediately *)
      seq_approx ~fwd_funcs (path_approx ~fwd_funcs body) f.next
  | Ireturn -> Return
  | Iop (Itailcall_ind) -> PRTC
  | Iop (Itailcall_imm {func; _}) ->
    if String.Set.mem func fwd_funcs then PRTC else Return
  | Iend -> Exit (IntSet.singleton 0)
  | Iexit i -> Exit (IntSet.singleton i)
  | Iraise _ -> Alloc (* Iraise included here because it has a poll inserted *)
  | Iop (Ialloc _ | Ipoll _) -> Alloc
  | Iop _ -> path_approx ~fwd_funcs f.next

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

let path_polls f =
  match path_approx ~fwd_funcs:String.Set.empty f with
  | Alloc -> true
  | _ -> false

let requires_prologue_poll ~future_funcnames f =
  match path_approx ~fwd_funcs:future_funcnames f with
  | PRTC -> true
  | _ -> false

(* This determines whether from a given instruction we unconditionally
   allocate and this is used to avoid adding polls unnecessarily *)
let polls_unconditionally (i : Mach.instruction) =
  path_polls i

(* returns a list of ids for the handlers of recursive catches from
   Mach instruction [f]. These are used to later add polls before
   exits to them. *)
let rec find_rec_handlers ~future_funcnames (f : Mach.instruction) =
  match f.desc with
  | Iifthenelse (_, ifso, ifnot) ->
      let ifso_rec_handlers = find_rec_handlers ~future_funcnames ifso in
      let ifnot_rec_handlers = find_rec_handlers ~future_funcnames ifnot in
      let next_rec_handlers = find_rec_handlers ~future_funcnames f.next in
      ifso_rec_handlers @ ifnot_rec_handlers @ next_rec_handlers
  | Iswitch (_, cases) ->
      let case_rec_handlers =
        Array.fold_left
          (fun agg_rec_handlers case ->
            agg_rec_handlers @ find_rec_handlers ~future_funcnames case)
          [] cases
      in
      case_rec_handlers @ find_rec_handlers ~future_funcnames f.next
  | Icatch (rec_flag, handlers, body) -> (
      match rec_flag with
      | Recursive ->
          let rec_handlers =
            List.map
              (fun (id, handler) ->
                let inner_rec_handlers = find_rec_handlers ~future_funcnames
                  handler in
                let current_rec_handlers =
                  if not (polls_unconditionally handler) then [ id ] else []
                in
                inner_rec_handlers @ current_rec_handlers)
              handlers
            |> List.flatten
          in
          let body_rec_handlers = find_rec_handlers ~future_funcnames body in
          body_rec_handlers @ rec_handlers @ find_rec_handlers
            ~future_funcnames f.next
      | Nonrecursive ->
          let non_rec_catch_handlers =
            List.fold_left
              (fun tmp_rec_handlers (_, handler) ->
                tmp_rec_handlers @ find_rec_handlers ~future_funcnames handler)
              [] handlers
          in
          let body_rec_handlers = find_rec_handlers ~future_funcnames body in
          body_rec_handlers @ non_rec_catch_handlers @ find_rec_handlers
            ~future_funcnames f.next
      )
  | Itrywith (body, handler) ->
      let handler_rec_handler = find_rec_handlers ~future_funcnames handler in
      let body_rec_handlers = find_rec_handlers ~future_funcnames body in
      body_rec_handlers @ handler_rec_handler @ find_rec_handlers
        ~future_funcnames f.next
  | Iexit _ | Iend | Ireturn
  | Iop (Itailcall_ind)
  | Iop (Itailcall_imm _)
  | Iraise _ ->
      []
  | Iop _ -> find_rec_handlers ~future_funcnames f.next

(* given the list of handler ids [rec_handlers] for recursive catches, add polls
   before backwards edges starting from Mach instruction [i] *)
let instrument_body_with_polls (rec_handlers : int list) (i : Mach.instruction)
    =
  (* the [current_handlers] list allows for an optimisation which avoids
    putting a poll before the first jump in to a loop *)
  let rec instrument_body (current_handlers : int list) (f : Mach.instruction) =
    let instrument_with_handlers i = instrument_body current_handlers i in
    match f.desc with
    | Iifthenelse (test, i0, i1) ->
        {
          f with
          desc = Iifthenelse (
            test, instrument_with_handlers i0, instrument_with_handlers i1
          );
          next = instrument_with_handlers f.next;
        }
    | Iswitch (index, cases) ->
        {
          f with
          desc = Iswitch (index, Array.map instrument_with_handlers cases);
          next = instrument_with_handlers f.next;
        }
    | Icatch (rec_flag, handlers, body) ->
        {
          f with
          desc =
            Icatch
              ( rec_flag,
                List.map
                  (fun (idx, instrs) ->
                    (idx, instrument_body (idx :: current_handlers) instrs))
                  handlers,
                instrument_with_handlers body );
          next = instrument_with_handlers f.next;
        }
    | Itrywith (body, handler) ->
        {
          f with
          desc = Itrywith (
            instrument_with_handlers body, instrument_with_handlers handler
          );
          next = instrument_with_handlers f.next;
        }
    | Iexit id ->
        let new_f = { f with next = instrument_with_handlers f.next } in
        if List.mem id current_handlers && List.mem id rec_handlers then
          Mach.instr_cons
            (Iop (Ipoll { return_label = None }))
            [||] [||] new_f
        else new_f
    | Iend | Ireturn | Iop (Itailcall_ind) | Iop (Itailcall_imm _) | Iraise _
      ->
        f
    | Iop _ -> { f with next = instrument_with_handlers f.next }
  in
  instrument_body [] i

let instrument_fundecl ~future_funcnames (i : Mach.fundecl) : Mach.fundecl =
  let f = i.fun_body in
  let rec_handlers = find_rec_handlers ~future_funcnames f in
  { i with fun_body = instrument_body_with_polls rec_handlers f }
