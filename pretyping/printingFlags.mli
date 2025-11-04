(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Detype : sig
  type t = {
    raw : bool;
    universes : bool;
    (** Should we print hidden sort quality variables? *)
    qualities : bool;
    relevances : bool;
    (** If true, prints full local context of evars *)
    evar_instances : bool;
    wildcard : bool;
    fast_names : bool;
    synth_match_return : bool;
    matching : bool;
    primproj_params : bool;
    unfolded_primproj_as_match : bool;
    match_paramunivs : bool;
  }

  val current : unit -> t
end

module Extern : sig
  module FactorizeEqns : sig
    type t = {
      raw : bool;
      (** If true, contract branches with same r.h.s. and same matching
          variables in a disjunctive pattern *)
      factorize_match_patterns : bool;
      (** If this flag is true and the last non unique clause of a
          "match" is a variable-free disjunctive pattern, turn it into a
          catch-call case *)
      allow_match_default_clause : bool;
    }

    val current : unit -> t
  end

  type t = {
    raw : bool;
    (** This tells to skip types if a variable has this type by default *)
    use_implicit_types : bool;
    records : bool;
    implicits : bool;
    (** When [implicits] is on then [implicits_explicit_args] tells
        how implicit args are printed. If on, implicit args are
        printed with the form (id:=arg) otherwise arguments are
        printed normally and the function is prefixed by "@". *)
    implicits_explicit_args : bool;
    (** Tells if implicit arguments not known to be inferable from a rigid
        position are systematically printed *)
    implicits_defensive : bool;
    coercions : bool;
    parentheses : bool;
    notations : bool;
    (** primitive tokens, like strings *)
    raw_literals : bool;
    (** This governs printing of projections using the dot notation symbols *)
    projections : bool;
    float : bool;
    factorize_eqns : FactorizeEqns.t;
    (* XXX depth? *)
  }

  val current : unit -> t
end

(* XXX don't use submodule for this? ie PrintingFlags.t = detype * extern etc  *)
module Combined : sig
  type t = {
    detype : Detype.t;
    extern : Extern.t;
  }

  val current : unit -> t
end

(** These flags are still accessed directly, but not when printing constr *)

(* Set Printing All flag. *)
val raw_print : bool ref

val print_universes : bool ref
