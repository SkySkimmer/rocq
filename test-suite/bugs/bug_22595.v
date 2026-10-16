Set Universe Polymorphism.
Variant Box A := box (x : A).

Fail Definition test@{u} (A : Type@{u}) : Set := Box A.
