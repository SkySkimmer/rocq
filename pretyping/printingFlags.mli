(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Set Printing All flag. *)
val raw_print : bool ref

val print_universes : bool ref

val print_coercions : bool ref

val print_parentheses : bool ref

(** When [print_implicits] is on then [print_implicits_explicit_args]
    tells how implicit args are printed. If on, implicit args are
    printed with the form (id:=arg) otherwise arguments are printed
    normally and the function is prefixed by "@". *)
val print_implicits_explicit_args : unit -> bool

val print_implicits : bool ref

(** Tells if implicit arguments not known to be inferable from a rigid
    position are systematically printed *)
val print_implicits_defensive : bool ref

(** This governs printing of projections using the dot notation symbols *)
val print_projections : bool ref

(** Negated version of Printing Notations (negated for convenience in Himsg.explicit_flags)  *)
val print_no_symbol : bool ref

(** Print primitive tokens, like strings *)
val print_raw_literal : bool ref

(** This tells to skip types if a variable has this type by default *)
val print_use_implicit_types : unit -> bool
