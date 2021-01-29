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

module StringSet = Set.Make (String)

(* Add a poll test and polling instruction before [f]. In the later
  linearisation pass this will simplify in to a conditional and backwards
  jump pair *)
let add_fused_poll_before (f : Mach.instruction) : Mach.instruction =
  let poll_instr =
    Mach.instr_cons
      (Iop (Ipollcall { check_young_limit = false; return_label = None }))
      [||] [||] (Mach.end_instr ())
  in
  Mach.instr_cons
    (Iifthenelse (Ipolltest Ipending, poll_instr, Mach.end_instr ()))
    [||] [||] f

(* Add a poll instruction which checks the young limit itself before [f] *)
let add_checked_poll_before check_young_limit (f : Mach.instruction)
      : Mach.instruction =
    Mach.instr_cons
      (Iop (Ipollcall { check_young_limit; return_label = None }))
      [||] [||] f

(* Check a sequence of instructions from [f] and return whether
   they poll (via an alloc or raising an exception) *)
let rec path_polls (f : Mach.instruction) : bool =
  match f.desc with
  | Iifthenelse (_, i0, i1) ->
      ((path_polls i0) && (path_polls i1)) || (path_polls f.next)
  | Iswitch (_, acts) ->
      (Array.for_all path_polls acts) && (path_polls f.next)
  | Icatch (_, handlers, body) ->
     (path_polls f.next) && (path_polls body)
     &&
     (List.for_all path_polls (List.map (fun (_, handler_code) ->
      handler_code) handlers))
  | Itrywith (body, handler) ->
      (path_polls body) && (path_polls handler) && (path_polls f.next)
  | Ireturn | Iend | Iexit _ -> false
  | Iop (Ialloc _) | Iraise _ -> true (* Iraise included here because
                                                it has a poll inserted *)
  | Iop _ -> path_polls f.next

 (* Check a sequence of instructions from [f] and return whether
   they poll (via an alloc or raising an exception) *)
let requires_prologue_poll ~future_funcnames (f : Mach.instruction) : bool =
  let rec check_path i =
  match i.desc with
  | Iifthenelse (_, i0, i1) ->
      (check_path i0) || (check_path i1) || (check_path i.next)
  | Iswitch (_, acts) ->
      (Array.exists check_path acts) || (check_path i.next)
  | Icatch (_, handlers, body) ->
     (check_path body)
     ||
      (List.exists check_path (List.map (fun (_, handler_code) ->
        handler_code) handlers)) || (check_path i.next)
  | Itrywith (body, handler) ->
      (check_path body) || (check_path handler) || (check_path i.next)
  | Iop (Itailcall_ind) -> true
  | Iop (Itailcall_imm { func; _ }) ->
    if (StringSet.mem func future_funcnames) then
      (* this means we have a call to a function that might be a self call
         or a call to a future function (which won't have a poll) *)
      true
    else
      check_path i.next
  | Iop (Ialloc _) | Iraise _ -> false (* Iraise included here because
                                                it has a poll inserted *)
  | Iend | Ireturn | Iexit _ -> false
  | Iop _ -> check_path i.next
  in check_path f

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
          add_fused_poll_before new_f
        else new_f
    | Iend | Ireturn | Iop (Itailcall_ind) | Iop (Itailcall_imm _)
      ->
        f
    | Iraise _ ->
      add_checked_poll_before true
        { f with next = instrument_with_handlers f.next }
    | Iop _ -> { f with next = instrument_with_handlers f.next }
  in
  instrument_body [] i

let instrument_fundecl ~future_funcnames (i : Mach.fundecl) : Mach.fundecl =
  let f = i.fun_body in
  let rec_handlers = find_rec_handlers ~future_funcnames f in
  { i with fun_body = instrument_body_with_polls rec_handlers f }
