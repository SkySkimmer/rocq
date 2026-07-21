(* A re-exports a safe-required library.  Compiling A records both the
   safe-require of CRelationClasses (so it stays safe for A's downstream
   users) and the standard ExportObject that re-exports it on [Import A]. *)
Require (safe) Export Corelib.Classes.CRelationClasses.
