(* B requires A fully.  Because A safe-required CRelationClasses, propagation
   keeps CRelationClasses safe in B's session too; before importing A only its
   fully-qualified names resolve. *)
Require A.

(* the qualified name resolves, the short one does not (safe = FQN only) *)
Check Corelib.Classes.CRelationClasses.flip.
Fail Check flip.

(* Importing A replays A's ExportObject; importing the safe-loaded
   CRelationClasses it carries hits the safe branch of Declaremods' import
   machinery (no ModObjs entry to collect) and pushes the short names.  This
   is only reachable with both Import/Export support and safe-dependency
   propagation: without propagation CRelationClasses would be fully loaded in
   B, without Import/Export support there would be no safe short-name walk. *)
Import A.
Check flip.

(* CRelationClasses is still only safe-loaded in B: no implicit arguments. *)
About Corelib.Classes.CRelationClasses.flip.

(* and a plain require of the propagated-safe library is still rejected *)
Fail Require Corelib.Classes.CRelationClasses.
