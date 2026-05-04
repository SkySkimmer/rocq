Section S.
  Variable rename : nat -> nat.
  Variable rename_inj : rename 0 = 0.

  Goal forall x y, x = S y -> False.
  Proof.
    intros x y H.
    generalize_eqs_vars H.
    Check rename_inj.
    Fail Check y.
  Abort.
End S.
