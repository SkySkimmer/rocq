(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)

Require Import ssreflect.
Require Import ssrbool TestSuite.ssr_mini_mathcomp.

Axiom P : forall T, seq T -> Prop.

Goal (forall T (s : seq T), P _ s).
move=> T s.
elim: s => [| x /lastP [| s] IH].
Admitted.

Goal forall x : 'I_1, x = 0 :> nat.
move=> /ord1 -> /=; exact: refl_equal.
Qed.

Goal forall x : 'I_1, x = 0 :> nat.
move=> x.
move=> /ord1 -> in x |- *.
exact: refl_equal.
Qed.
