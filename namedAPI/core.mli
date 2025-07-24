(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr

(**

This interface is inspired from work by Weituo DAI, and Yannick Forester

#############################
###      Constrains       ###
#############################

1. Be able to refer to variables indirectly by names
2. Keep track of the old variables for weakening
3. Be able to replace variables by term on the fly


#############################
###   Backend interface   ###
#############################

(* 0. Datastructre and General Purposed Functions *)
- state_decl : Type
- state : Type
- init_state : state

(* 1. General Purposed Functions *)
- add_idecl : state_decl -> state -> state
- add_pdecl : state_pdecl -> state -> state

(* 2. Debug and Printing Functions *)
- state_to_term : state -> list term

**)

type state =
{ state_context : rel_context;
  state_subst : constr list;
}

val init_state : state
