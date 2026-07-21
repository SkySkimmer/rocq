(* Control: fully requiring CRelationClasses before A makes it fully loaded;
   requiring A then reuses the full library silently. *)
Require Corelib.Classes.CRelationClasses.
Require A.
About Corelib.Classes.CRelationClasses.flip.
