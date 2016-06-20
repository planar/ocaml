(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Sébastien Hinderer, projet Gallium, INRIA Paris           *)
(*                                                                        *)
(*   Copyright 2016 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Definition of a few builtin actions *)

val compile_bytecode_with_bytecode_compiler : Actions.t
val compile_bytecode_with_nativecode_compiler : Actions.t
val compile_nativecode_with_bytecode_compiler : Actions.t
val compile_nativecode_with_nativecode_compiler : Actions.t

val execute : Actions.t
val check_program_output : Actions.t
