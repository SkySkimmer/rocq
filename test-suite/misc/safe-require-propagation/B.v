(* A was compiled with [Require (safe) CMorphisms]: requiring A fully must
   still keep CRelationClasses (a safe dependency, reached only through the
   safe-required CMorphisms) safe. *)
Require A.

(* no implicit arguments, but can be used *)
Type Corelib.Classes.CRelationClasses.flip.
About Corelib.Classes.CRelationClasses.flip.

(* a plain require of a propagated-safe library is still rejected *)
Fail Require Corelib.Classes.CRelationClasses.
