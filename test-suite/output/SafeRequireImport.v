(* Test Import/Export support for Require (safe).
   See also output/SafeRequire.v for the plain (no-import) behaviour. *)

(* 1. Plain Require (safe): only fully-qualified names are visible.
   The short name [flip] does not resolve, the qualified one does. *)
Require (safe) CRelationClasses.
Fail Check flip.
Check CRelationClasses.flip.

(* 2. A standalone Import on the already safe-loaded library pushes the
   short names (this exercises the safe branch of Declaremods' import
   machinery, since the library has no ModObjs entry). *)
Import CRelationClasses.
Check flip.

(* 3. Require (safe) Import: the short name is available immediately. *)
Require (safe) Import CMorphisms.
Check respectful.

(* 4. Require (safe) Export: like Import for the current session, and
   records the standard ExportObject for re-export downstream. *)
Require (safe) Export CRelationClasses.
Check arrow.

(* 5. The From ... Require (safe) Import form also parses and imports. *)
From Corelib Require (safe) Import RelationClasses.
Check unary_operation.

(* A plain Require of a safe-imported library still errors. *)
Fail Require CRelationClasses.
