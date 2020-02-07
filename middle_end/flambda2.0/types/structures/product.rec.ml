(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                   Mark Shinwell, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2019 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-30-40-41-42"]

module K = Flambda_kind
module T = Type_grammar
module TEE = Typing_env_extension

module Make (Index : Identifiable.S) = struct

  (* Product are a set of constraints: each new field reduces the
     concrete set. The empty product is Top. There is no bottom. All
     components must be of the same kind.

     { 1 => Unknown; 2 => V } is equal to { 2 => V } *)
  type t = {
    components_by_index : T.t Index.Map.t;
    kind : Flambda_kind.t;
  }

  let print ppf { components_by_index; kind = _ } =
    Format.fprintf ppf
      "@[<hov 1>(\
        @[<hov 1>(components_by_index@ %a)@]\
        )@]"
      (Index.Map.print Type_grammar.print) components_by_index

  let print_with_cache ~cache:_ ppf t = print ppf t

  let create kind components_by_index =
    (* CR mshinwell: Check that the types are all of the same kind *)
    { components_by_index;
      kind;
    }

  let create_bottom _ = assert false

  (* CR mshinwell: This "bottom" stuff is still dubious.
     We can't treat 0-sized blocks as bottom; it's legal to bind one of
     those (e.g. an empty module). *)

  let is_bottom t =
    Index.Map.exists (fun _ typ -> Type_grammar.is_obviously_bottom typ)
      t.components_by_index

  let width t =
    Targetint.OCaml.of_int (Index.Map.cardinal t.components_by_index)

  let components t = Index.Map.data t.components_by_index

  let meet env
        { components_by_index = components_by_index1; kind = kind1; }
        { components_by_index = components_by_index2; kind = kind2; }
    : _ Or_bottom.t =
    if not (Flambda_kind.equal kind1 kind2) then
      Misc.fatal_errorf "Product.meet between unmatching kinds %a and %a@."
        Flambda_kind.print kind1 Flambda_kind.print kind2;
    let all_bottom = ref true in
    let env_extension = ref (TEE.empty ()) in
    let components_by_index =
      Index.Map.merge (fun _index ty1_opt ty2_opt ->
          match ty1_opt, ty2_opt with
          | None, None | Some _, None | None, Some _ -> None
          | Some ty1, Some ty2 ->
            let ty, env_extension' = Type_grammar.meet' env ty1 ty2 in
            env_extension := TEE.meet env !env_extension env_extension';
            if not (Type_grammar.is_obviously_bottom ty) then begin
              all_bottom := false
            end;
            Some ty)
        components_by_index1
        components_by_index2
    in
    if !all_bottom && Index.Map.cardinal components_by_index > 0 then Bottom
    else Ok ({ components_by_index; kind = kind1; }, !env_extension)

  let join env
        { components_by_index = components_by_index1; kind = kind1; }
        { components_by_index = components_by_index2; kind = kind2; } =
    if not (Flambda_kind.equal kind1 kind2) then
      Misc.fatal_errorf "Product.meet between unmatching kinds %a and %a@."
        Flambda_kind.print kind1 Flambda_kind.print kind2;
    let components_by_index =
      Index.Map.merge (fun _index ty1_opt ty2_opt ->
          match ty1_opt, ty2_opt with
          | None, None -> None
          | Some ty, None | None, Some ty -> Some ty
          | Some ty1, Some ty2 -> Some (Type_grammar.join' env ty1 ty2))
        components_by_index1
        components_by_index2
    in
    { components_by_index; kind = kind1; }

  let apply_name_permutation ({ components_by_index; kind; } as t) perm =
    let components_by_index' =
      Index.Map.map_sharing (fun typ ->
          Type_grammar.apply_name_permutation typ perm)
        components_by_index
    in
    if components_by_index == components_by_index' then t
    else { components_by_index = components_by_index'; kind = kind; }

  let free_names { components_by_index; kind = _; } =
    Index.Map.fold (fun _index ty free_names ->
        Name_occurrences.union (Type_grammar.free_names ty) free_names)
      components_by_index
      Name_occurrences.empty

  let map_types ({ components_by_index; kind } as t)
        ~(f : Type_grammar.t -> Type_grammar.t Or_bottom.t)
        : _ Or_bottom.t =
    let found_bottom = ref false in
    let components_by_index' =
      Index.Map.map_sharing (fun ty ->
          match f ty with
          | Bottom ->
            found_bottom := true;
            ty
          | Ok ty -> ty)
        components_by_index
    in
    if !found_bottom then Bottom
    else if components_by_index == components_by_index' then Ok t
    else Ok { components_by_index = components_by_index'; kind; }

  let to_map t = t.components_by_index
end

module Int_indexed = Make (Numbers.Int)

module Closure_id_indexed = Make (Closure_id)

module Var_within_closure_indexed = Make (Var_within_closure)
