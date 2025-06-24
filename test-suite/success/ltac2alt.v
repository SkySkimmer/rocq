

Require Import Ltac2.Ltac2.

Ltac2 Notation "we" "claim" "that" c(lconstr) : alt(1) := assert $c.

Set Default Proof Mode "Ltac2Alt".

Goal True.
  we claim that False.
Abort.
