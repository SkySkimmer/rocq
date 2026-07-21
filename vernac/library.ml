(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util

open Names
open Libobject

(************************************************************************)
(*s Low-level interning/externing of libraries to files *)

let raw_extern_library f =
  ObjFile.open_out ~file:f

let raw_intern_library ?loc f =
  System.with_magic_number_check ?loc
   (fun file -> ObjFile.open_in ~file) f

(************************************************************************)
(** Serialized objects loaded on-the-fly *)

exception Faulty of string

module Delayed :
sig

type 'a delayed
val in_delayed : string -> ObjFile.in_handle -> segment:'a ObjFile.id -> 'a delayed * Digest.t
val fetch_delayed : 'a delayed -> 'a

end =
struct

type 'a delayed = {
  del_file : string;
  del_off : int64;
  del_digest : Digest.t;
}

let in_delayed f ch ~segment =
  let seg = ObjFile.get_segment ch ~segment in
  let digest = seg.ObjFile.hash in
  { del_file = f; del_digest = digest; del_off = seg.ObjFile.pos; }, digest

(** Fetching a table of opaque terms at position [pos] in file [f],
    expecting to find first a copy of [digest]. *)

let fetch_delayed del =
  let { del_digest = digest; del_file = f; del_off = pos; } = del in
  let ch = open_in_bin f in
  let obj, digest' =
    try
      let () = LargeFile.seek_in ch pos in
      let obj = System.marshal_in f ch in
      let digest' = Digest.input ch in
      obj, digest'
    with e -> close_in ch; raise e
  in
  close_in ch;
  if not (String.equal digest digest') then raise (Faulty f);
  obj

end

open Delayed


(************************************************************************)
(*s Modules on disk contain the following informations (after the magic
    number, and before the digest). *)

type compilation_unit_name = DirPath.t

type library_disk = {
  md_compiled : Safe_typing.compiled_library;
  md_syntax_objects : Declaremods.library_objects;
  md_objects : Declaremods.library_objects;
}

type summary_disk = {
  md_name : compilation_unit_name;
  md_deps : (compilation_unit_name * Safe_typing.vodigest) array;
  md_ocaml : string;
  md_info : Library_info.t;
  (* Subset of the direct dependencies (i.e. of the dirpaths appearing in
     [md_deps]) that were only safe-required (SafeLoaded) when this library
     was compiled. Downstream requires must keep these dependencies safe. *)
  md_safe_deps : DirPath.Set.t;
}

(*s Modules loaded in memory contain the following informations. They are
    kept in the global table [libraries_table]. *)

type library_t = {
  library_name : compilation_unit_name;
  library_data : library_disk;
  library_deps : (compilation_unit_name * Safe_typing.vodigest) array;
  library_safe_deps : DirPath.Set.t;
  library_digests : Safe_typing.vodigest;
  library_info : Library_info.t;
  library_vm : Vmlibrary.on_disk;
}

type load_status = FullLoaded | SafeLoaded

(* This is a map from names to loaded libraries *)
let libraries_table : (load_status * library_t) DirPath.Map.t ref =
  Summary.ref DirPath.Map.empty ~stage:Summary.Stage.Synterp ~name:"LIBRARY"

(* This is the map of loaded libraries filename *)
(* (not synchronized so as not to be caught in the states on disk) *)
let libraries_filename_table = ref DirPath.Map.empty

(* These are the _ordered_ sets of loaded libraries *)
let libraries_loaded_list = Summary.ref [] ~stage:Summary.Stage.Synterp ~name:"LIBRARY-LOAD"

let loaded_native_libraries = Summary.ref DirPath.Set.empty ~stage:Summary.Stage.Interp ~name:"NATIVE-LIBRARY-LOAD"

(* Opaque proof tables *)

(* various requests to the tables *)

let find_library dir =
  DirPath.Map.find_opt dir !libraries_table

let try_find_library dir =
  match find_library dir with
  | Some lib -> lib
  | None ->
    user_err
      (str "Unknown library " ++ DirPath.print dir ++ str ".")

let library_compiled dir =
  let _, lib = Option.get @@ find_library dir in
  lib.library_data.md_compiled

let register_library_filename dir f =
  (* Not synchronized: overwrite the previous binding if one existed *)
  (* from a previous play of the session *)
  libraries_filename_table :=
    DirPath.Map.add dir f !libraries_filename_table

let library_full_filename dir =
  try DirPath.Map.find dir !libraries_filename_table
  with Not_found -> "<unavailable filename>"

let library_is_loaded dir =
  try let _ = find_library dir in true
  with Not_found -> false

  (* If a library is loaded several time, then the first occurrence must
     be performed first, thus the libraries_loaded_list ... *)

let register_loaded_library ~root load_status m =
  let libname = m.library_name in
  let rec aux = function
    | [] -> [root, libname]
    | (_, m') ::_ as l when DirPath.equal m' libname -> l
    | m'::l' -> m' :: aux l' in
  libraries_loaded_list := aux !libraries_loaded_list;
  libraries_table := DirPath.Map.add libname (load_status, m) !libraries_table

let register_native_library libname =
  if (Global.typing_flags ()).enable_native_compiler
    && not (DirPath.Set.mem libname !loaded_native_libraries) then begin
      let dirname = Filename.dirname (library_full_filename libname) in
      loaded_native_libraries := DirPath.Set.add libname !loaded_native_libraries;
      Nativelib.enable_library dirname libname
  end

let loaded_libraries () = List.map snd !libraries_loaded_list

(** Delayed / available tables of opaque terms *)

type table_status =
  | ToFetch of Opaques.opaque_disk delayed
  | Fetched of Opaques.opaque_disk

let opaque_tables =
  ref (DirPath.Map.empty : table_status DirPath.Map.t)

let add_opaque_table dp st =
  opaque_tables := DirPath.Map.add dp st !opaque_tables

let access_table what tables dp i =
  let t = match DirPath.Map.find dp !tables with
    | Fetched t -> t
    | ToFetch f ->
      let dir_path = Names.DirPath.to_string dp in
      Flags.if_verbose Feedback.msg_info (str"Fetching " ++ str what++str" from disk for " ++ str dir_path);
      let t =
        try fetch_delayed f
        with Faulty f ->
          user_err
            (str "The file " ++ str f ++ str " (bound to " ++ str dir_path ++
             str ") is corrupted,\ncannot load some " ++
             str what ++ str " in it.\n")
      in
      tables := DirPath.Map.add dp (Fetched t) !tables;
      t
  in
  Opaques.get_opaque_disk i t

let access_opaque_table o =
  let (sub, ci, dp, i) = Opaqueproof.repr o in
  let ans =
    if DirPath.equal dp (Global.current_dirpath ()) then
      Opaques.get_current_opaque i
    else
      let what = "opaque proofs" in
      access_table what opaque_tables dp i
  in
  match ans with
  | None -> None
  | Some (c, ctx) ->
    let (c, ctx) = Discharge.cook_opaque_proofterm ci (c, ctx) in
    let c = Mod_subst.subst_mps_list sub c in
    Some (c, ctx)

let indirect_accessor = {
  Global.access_proof = access_opaque_table;
}

(************************************************************************)
(* Internalise libraries *)

type seg_sum = summary_disk
type seg_lib = library_disk
type seg_proofs = Opaques.opaque_disk
type seg_vm = Vmlibrary.compiled_library

let mk_library sd md digests vm =
  {
    library_name     = sd.md_name;
    library_data     = md;
    library_deps     = sd.md_deps;
    library_safe_deps = sd.md_safe_deps;
    library_digests  = digests;
    library_info     = sd.md_info;
    library_vm = vm;
  }

let mk_intern_library sum lib digest_lib proofs vm =
  add_opaque_table sum.md_name (ToFetch proofs);
  let open Safe_typing in
  mk_library sum lib (Dvo_or_vi digest_lib) vm

let summary_seg : seg_sum ObjFile.id = ObjFile.make_id "summary"
let library_seg : seg_lib ObjFile.id = ObjFile.make_id "library"
let opaques_seg : seg_proofs ObjFile.id = ObjFile.make_id "opaques"
let vm_seg : seg_vm ObjFile.id = Vmlibrary.vm_segment

module Intern = struct
  module Provenance = struct
    type t = string * string
    (** A pair of [kind, object], for example ["file",
        "/usr/local/foo.vo"], used for error messages. *)
  end

  type t = DirPath.t -> (library_t, Exninfo.iexn) Result.t * Provenance.t
end

let intern_from_file file =
  let ch = raw_intern_library file in
  let lsd, digest_lsd = ObjFile.marshal_in_segment ch ~segment:summary_seg in
  let lmd, digest_lmd = ObjFile.marshal_in_segment ch ~segment:library_seg in
  let del_opaque, _ = in_delayed file ch ~segment:opaques_seg in
  let vmlib = Vmlibrary.load lsd.md_name ~file ch in
  ObjFile.close_in ch;
  System.check_caml_version ~caml:lsd.md_ocaml ~file;
  register_library_filename lsd.md_name file;
  Library_info.warn_library_info ~transitive:true lsd.md_name lsd.md_info;
  mk_intern_library lsd lmd digest_lmd del_opaque vmlib

let intern_from_file file =
  let provenance = ("file", file) in
  (* This is a barrier to catch IO / Marshal exceptions in a more
     structured way, as to provide better error messages. *)
  (match CErrors.to_result ~f:intern_from_file file with
   | Ok res -> Ok res
   | Error iexn -> Error iexn), provenance

let check_library_expected_name ~provenance dir library_name =
  if not (DirPath.equal dir library_name) then
    let kind, obj = provenance in
    user_err
      (str "The " ++ str kind ++ str " " ++ str obj ++ str " contains library" ++ spc () ++
       DirPath.print library_name ++ spc () ++ str "and not library" ++
       spc() ++ DirPath.print dir ++ str ".")

exception InternError of { exn : exn; provenance : Intern.Provenance.t; dir : DirPath.t }

let () = CErrors.register_handler (function
    | InternError { exn; provenance; dir } ->
      let err = CErrors.print exn in
      Some (Pp.(str "Error when parsing .vo (from " ++ str (fst provenance) ++ str " " ++
                str (snd provenance) ++ str ") for library " ++ Names.DirPath.print dir ++ str ": " ++ err))
    | _ -> None)

let error_in_intern provenance dir (exn, info) =
  Exninfo.iraise (InternError { exn; provenance; dir }, info)

(* Intern a library and its dependency closure.

   Unlike a plain load, safe-ness is not decided during interning: we
   first intern the whole closure (skipping already-loaded libraries,
   whose dependencies are already loaded), and only afterwards compute a
   per-library effective mode (see [compute_modes]) from the recorded
   safe-dependency edges. This keeps a safe dependency of a fully-loaded
   library safe for the current session too. *)
let rec intern_library ~intern (needed, contents as acc) dir =
  (* Look if in the current logical environment: already-loaded libraries
     (whether full or safe) are terminal, their deps are already loaded. *)
  match find_library dir with
  | Some _ -> acc
  | None ->
    (* Look if already listed in the accumulator *)
    match DirPath.Map.find_opt dir contents with
    | Some _ ->
      acc
    | None ->
      (* We intern the library, and then intern the deps *)
      match intern dir with
      | Ok m, provenance ->
        check_library_expected_name ~provenance dir m.library_name;
        intern_library_deps ~intern acc dir m
      | Error iexn, provenance ->
        error_in_intern provenance dir iexn

and intern_library_deps ~intern (needed, contents) dir m =
  let contents = DirPath.Map.add dir m contents in
  let needed, contents =
    Array.fold_left (intern_mandatory_library ~intern dir)
      (needed, contents) m.library_deps in
  ((false, dir) :: needed, contents)

and intern_mandatory_library ~intern caller (needed, contents) (dir,d) =
  let needed, contents = intern_library ~intern (needed, contents) dir in
  let digest = digest_of_dep ~contents dir in
  let () = if not (Safe_typing.digest_match ~actual:digest ~required:d) then
    let from = library_full_filename caller in
    user_err
      (str "Compiled library " ++ DirPath.print caller ++
       str " (in file " ++ str from ++
       str ") makes inconsistent assumptions over library " ++
       DirPath.print dir)
  in
  (needed, contents)

and digest_of_dep ~contents dir =
  match DirPath.Map.find_opt dir contents with
  | Some m -> m.library_digests
  | None ->
    match find_library dir with
    | Some (_, m) -> m.library_digests
    | None ->
      anomaly Pp.(str "Missing library " ++ DirPath.print dir ++
                  str " while interning dependencies.")

let rec_intern_library ~intern (needed, contents) (_loc, dir) =
  intern_library ~intern (needed, contents) dir

(* [needed] is built dependencies-first (each dir is prepended after its
   deps). A dir added as a dependency and then reached again as a root keeps
   its original (earlier) position; mark such positions as roots. *)
let promote_roots needed roots =
  let roots = List.fold_left (fun s d -> DirPath.Set.add d s) DirPath.Set.empty roots in
  List.map (fun (root, d) -> (root || DirPath.Set.mem d roots), d) needed

(* Effective load mode computed for each library of an interned closure. *)
type require_mode = ModeFull | ModeSafe

(* Compute, for each newly-interned library of the closure, whether it must
   be fully loaded or may be safe-loaded.

   Roots get the command mode ([ModeFull] for [Require], [ModeSafe] for
   [Require (safe)]). An edge A -> D is "safe" iff D belongs to A's recorded
   safe dependencies ([library_safe_deps]), otherwise "normal". A library is
   [ModeFull] iff it is reachable from a [ModeFull] root through a chain of
   normal edges; otherwise it is [ModeSafe].

   Fullness only grows, so this is a monotone fixpoint reached by a worklist
   seeded with the full roots and propagated along normal edges. *)
let compute_modes ~cmd_safe ~roots contents =
  let full = ref DirPath.Set.empty in
  let queue = Queue.create () in
  let mark dir =
    if DirPath.Map.mem dir contents && not (DirPath.Set.mem dir !full) then begin
      full := DirPath.Set.add dir !full;
      Queue.add dir queue
    end
  in
  if not cmd_safe then List.iter mark roots;
  while not (Queue.is_empty queue) do
    let dir = Queue.pop queue in
    let m = DirPath.Map.find dir contents in
    Array.iter (fun (d, _) ->
        if not (DirPath.Set.mem d m.library_safe_deps) then mark d)
      m.library_deps
  done;
  fun dir -> if DirPath.Set.mem dir !full then ModeFull else ModeSafe

let error_previously_safe_required dir =
  CErrors.user_err
    Pp.(str "Cannot unsafe-require library " ++ DirPath.print dir ++ spc() ++
        str "because it was previously required with (safe).")

(* Detect in-session conflicts with already-loaded libraries, i.e. a full
   demand (a full root, or a normal edge from a full library) reaching a
   library that was previously safe-required.

   This is a pre-order depth-first traversal from the roots along full
   (normal-edge) reachability, following each library's dependencies in
   declaration order, so that the offending library reported is the first
   one a plain require would have reached. *)
let check_closure_conflicts ~cmd_safe ~roots contents =
  let visited = ref DirPath.Set.empty in
  let rec visit dir =
    match find_library dir with
    | Some (SafeLoaded, _) -> error_previously_safe_required dir
    | Some (FullLoaded, _) -> ()
    | None ->
      if not (DirPath.Set.mem dir !visited) then begin
        visited := DirPath.Set.add dir !visited;
        let m = DirPath.Map.find dir contents in
        Array.iter (fun (d, _) ->
            if not (DirPath.Set.mem d m.library_safe_deps) then visit d)
          m.library_deps
      end
  in
  if not cmd_safe then List.iter visit roots

(* Intern the closure of [modrefl], compute per-library modes, run the
   in-session conflict checks and return the topologically-ordered list of
   newly-interned libraries tagged with their computed mode. *)
let intern_and_resolve_modes ~cmd_safe ~intern modrefl =
  let needed, contents =
    List.fold_left (rec_intern_library ~intern) ([], DirPath.Map.empty) modrefl in
  let roots = List.map snd modrefl in
  let needed = promote_roots needed roots in
  List.iter (fun dir ->
      let info = match DirPath.Map.find_opt dir contents with
        | Some m -> Some m.library_info
        | None -> Option.map (fun (_, m) -> m.library_info) (find_library dir)
      in
      Option.iter (Library_info.warn_library_info dir) info)
    roots;
  let mode_of = compute_modes ~cmd_safe ~roots contents in
  check_closure_conflicts ~cmd_safe ~roots contents;
  List.rev_map (fun (root, dir) ->
      let m = DirPath.Map.find dir contents in
      (mode_of dir, root, m))
    needed

let native_name_from_filename f =
  let ch = raw_intern_library f in
  let lmd, digest_lmd = ObjFile.marshal_in_segment ch ~segment:summary_seg in
  Nativecode.mod_uid_of_dirpath lmd.md_name

(**********************************************************************)
(*s [require_library] loads and possibly opens a library. This is a
    synchronized operation. It is performed as follows:

  preparation phase: (functions require_library* ) the library and its
    dependencies are read from to disk (using intern_* )
    [they are read from disk to ensure that at section/module
     discharging time, the physical library referred to outside the
     section/module is the one that was used at type-checking time in
     the section/module]

  execution phase: (through add_leaf and cache_require)
    the library is loaded in the environment and Nametab, the objects are
    registered etc, using functions from Declaremods (via load_library,
    which recursively loads its dependencies)
*)

(* Full-mode registration (object replay). *)

let register_library m =
  let l = m.library_data in
  Declaremods.Interp.register_library
    m.library_name
    l.md_compiled
    l.md_objects
    m.library_digests
    m.library_vm
  ;
  register_native_library m.library_name

let register_library_syntax ~root m =
  let l = m.library_data in
  Declaremods.Synterp.register_library
    m.library_name
    l.md_syntax_objects;
  register_loaded_library ~root FullLoaded m

(* Safe-mode registration: import the kernel structure and push FQN-only names
   without replaying libobjects. *)

let safe_require_mind_names vis sp mind mib =
  mib.Declarations.mind_packets |> Array.iteri @@ fun ind (mip:Declarations.one_inductive_body) ->
  let ind = (mind, ind) in
  let () = Nametab.push vis (Libnames.add_path_suffix sp mip.mind_typename) (IndRef ind) in
  mip.mind_consnames |> Array.iteri @@ fun ctor cna ->
  Nametab.push vis (Libnames.add_path_suffix sp cna) (ConstructRef (ind, ctor+1))

let rec safe_require_mod_names ~stage i sp mp mb =
  let () = match stage with
    | Summary.Stage.Synterp -> Nametab.push_module (Until i) sp mp
    | Interp -> ()
  in
  match Mod_declarations.mod_type mb with
  | MoreFunctor _ -> ()
  | NoFunctor contents ->
    contents |> List.iter @@ fun (lab, contents) ->
    match contents with
    | Declarations.SFBrules _ ->
      ()
    | SFBconst _ ->
      begin match stage with
      | Synterp -> ()
      | Interp ->
        let kn = Global.constant_of_delta_kn (KerName.make mp lab) in
        let sp = Libnames.add_path_suffix sp lab in
        Nametab.push (Until (i+1)) sp (ConstRef kn)
      end
    | SFBmind mib ->
      begin match stage with
      | Synterp -> ()
      | Interp ->
        let mind = Global.mind_of_delta_kn (KerName.make mp lab) in
        safe_require_mind_names (Until (i+1)) sp mind mib
      end
    | SFBmodtype _ ->
      begin match stage with
      | Synterp ->
        let mp = ModPath.MPdot (mp, lab) in
        let sp = Libnames.add_path_suffix sp lab in
        Nametab.push_modtype (Until (i+1)) sp mp
      | Interp -> ()
      end
    | SFBmodule mb ->
      safe_require_mod_names ~stage (i+1) (Libnames.add_path_suffix sp lab) (MPdot (mp,lab)) mb

let safe_require_names ~stage dp mb =
  let mp = ModPath.MPfile dp in
  let sp = Libnames.make_path0 dp in
  safe_require_mod_names ~stage 1 sp mp mb

let register_safe_library_syntax ~root m =
  safe_require_names ~stage:Synterp m.library_name
    (Safe_typing.module_of_library m.library_data.md_compiled);
  register_loaded_library ~root SafeLoaded m

let register_safe_library m =
  let compiled = m.library_data.md_compiled in
  let () =
    let mp = MPfile m.library_name in
    try
      (* If the library was loaded inside a module or section, the
         end_segment will replay the library object for non-kernel
         effects but the kernel did not forget the library. *)
      ignore(Global.lookup_module mp);
    with Not_found ->
      let mp' = Global.import compiled m.library_vm m.library_digests in
      if not (ModPath.equal mp mp') then
        anomaly (Pp.str "Unexpected disk module name.")
  in
  safe_require_names ~stage:Interp m.library_name
    (Safe_typing.module_of_library compiled);
  register_native_library m.library_name

(* Unified require objects. A single [Require] / [Require (safe)] now
   registers a whole topologically-ordered closure in which each library
   carries its computed mode: full libraries replay their objects, safe ones
   are only imported kernel-side. Interleaving the two in one object preserves
   the order (a full library's object replay may rely on an earlier one). *)

let register_one_syntax (mode, root, m) = match mode with
  | ModeFull -> register_library_syntax ~root m
  | ModeSafe -> register_safe_library_syntax ~root m

let register_one_interp (mode, m) = match mode with
  | ModeFull -> register_library m
  | ModeSafe -> register_safe_library m

(* Follow the semantics of Anticipate object:
   - called at module or module type closing when a Require occurs in
     the module or module type
   - not called from a library (i.e. a module identified with a file)
   [needed] is the ordered list of libraries not already loaded *)
let cache_require needed =
  List.iter register_one_interp needed

let load_require _ o =
  cache_require o

(* open_function is never called from here because an Anticipate object *)

type require_obj = (require_mode * library_t) list

let in_require : require_obj -> obj =
  declare_object
    {(default_object "REQUIRE") with
     cache_function = cache_require;
     load_function = load_require;
     open_function = (fun _ _ -> assert false);
     discharge_function = (fun o -> Some o);
     classify_function = (fun o -> Anticipate) }

let cache_require_syntax needed =
  List.iter register_one_syntax needed

let load_require_syntax _ o =
  cache_require_syntax o

(* open_function is never called from here because an Anticipate object *)

type require_obj_syntax = (require_mode * bool * library_t) list

let in_require_syntax : require_obj_syntax -> obj =
  declare_object
    {(default_object "REQUIRE-SYNTAX") with
     object_stage = Summary.Stage.Synterp;
     cache_function = cache_require_syntax;
     load_function = load_require_syntax;
     open_function = (fun _ _ -> assert false);
     discharge_function = (fun o -> Some o);
     classify_function = (fun o -> Anticipate) }

(* Require libraries, import them if [export <> None], mark them for export
   if [export = Some true] *)

let warn_require_in_module =
  CWarnings.create ~name:"require-in-module" ~category:CWarnings.CoreCategories.fragile
    (fun () -> strbrk "Use of “Require” inside a module is fragile." ++ spc() ++
               strbrk "It is not recommended to use this functionality in finished proof scripts.")

let require_library needed =
  if Lib.is_module_or_modtype () then warn_require_in_module ();
  Lib.add_leaf (in_require needed)

let require_library_syntax_from_dirpath ~cmd_safe ~intern modrefl =
  let needed = intern_and_resolve_modes ~cmd_safe ~intern modrefl in
  Lib.add_leaf (in_require_syntax needed);
  List.map (fun (mode, _root, m) -> (mode, m)) needed

(************************************************************************)
(*s [save_library dir] ends library [dir] and save it to the disk. *)

let current_deps () =
  (* Only keep the roots of the dependency DAG *)
  let map (root, m) =
    if root then
      let _, m = try_find_library m in
      Some (m.library_name, m.library_digests)
    else None
  in
  List.map_filter map !libraries_loaded_list

let current_safe_deps () =
  (* Among the direct dependencies (the roots of the DAG), record those that
     are only safe-loaded so that downstream requires keep them safe. *)
  let add acc (root, m) =
    if root then
      match find_library m with
      | Some (SafeLoaded, _) -> DirPath.Set.add m acc
      | Some (FullLoaded, _) | None -> acc
    else acc
  in
  List.fold_left add DirPath.Set.empty !libraries_loaded_list

let error_recursively_dependent_library dir =
  user_err
    (strbrk "Unable to use logical name " ++ DirPath.print dir ++
     strbrk " to save current library because" ++
     strbrk " it already depends on a library of this name.")

type 'doc todo_proofs =
 | ProofsTodoNone (* for .vo *)
 | ProofsTodoSomeEmpty of Future.UUIDSet.t (* for .vos *)

(* We now use two different digests in a .vo file. The first one
   only covers half of the file, without the opaque table. It is
   used for identifying this version of this library : this digest
   is the one leading to "inconsistent assumptions" messages.
   The other digest comes at the very end, and covers everything
   before it. This one is used for integrity check of the whole
   file when loading the opaque table. *)

(* Security weakness: file might have been changed on disk between
   writing the content and computing the checksum... *)

(* EJGA: would be nice maybe to have a version that performs extra
   cleanup in the case the computation raises? *)
let save_library_base f sum lib proofs vmlib =
  try
    let open Memprof_coq.Resource_bind in
    let& ch = Memprof_coq.Masking.with_resource ~acquire:raw_extern_library ~release:ObjFile.close_out f in
    ObjFile.marshal_out_segment ch ~segment:summary_seg sum;
    ObjFile.marshal_out_segment ch ~segment:library_seg lib;
    ObjFile.marshal_out_segment ch ~segment:opaques_seg proofs;
    ObjFile.marshal_out_segment ch ~segment:vm_seg vmlib
  with exn ->
    let iexn = Exninfo.capture exn in
    Sys.remove f;
    Exninfo.iraise iexn

(* This is the basic vo save structure *)
let save_library_struct ~output_native_objects dir =
  let md_compiled, md_objects, md_syntax_objects, vmlib, ast, info =
    Declaremods.end_library ~output_native_objects dir in
  let sd =
    { md_name = dir
    ; md_deps = Array.of_list (current_deps ())
    ; md_ocaml = Coq_config.caml_version
    ; md_info = info
    ; md_safe_deps = current_safe_deps ()
    } in
  let md =
    { md_compiled
    ; md_syntax_objects
    ; md_objects
    } in
  if Array.exists (fun (d,_) -> DirPath.equal d dir) sd.md_deps then
    error_recursively_dependent_library dir;
  sd, md, vmlib, ast

let save_library dir : library_t =
  let sd, md, vmlib, _ast = save_library_struct ~output_native_objects:false dir in
  (* Digest for .vo files is on the md part, for now we also play it
     safe when we work on-memory and compute the digest for the lib
     part, even if that's slow. Better safe than sorry. *)
  let digest = Marshal.to_string md [] |> Digest.string in
  mk_library sd md (Dvo_or_vi digest) (Vmlibrary.inject vmlib)

let save_library_to todo_proofs ~output_native_objects dir f =
  assert(
    let expected_extension = match todo_proofs with
      | ProofsTodoNone -> ".vo"
      | ProofsTodoSomeEmpty _ -> ".vos"
      in
    Filename.check_suffix f expected_extension);
  let except = match todo_proofs with
    | ProofsTodoNone -> Future.UUIDSet.empty
    | ProofsTodoSomeEmpty except -> except
    in
  (* Ensure that the call below is performed with all opaques joined *)
  let () = Opaques.Summary.join ~except () in
  let opaque_table, f2t_map = Opaques.dump ~except () in
  let () = assert (not (Future.UUIDSet.is_empty except) ||
    Safe_typing.is_joined_environment (Global.safe_env ()))
  in
  let sd, md, vmlib, ast = save_library_struct ~output_native_objects dir in
  (* Writing vo payload *)
  save_library_base f sd md opaque_table vmlib;
  (* Writing native code files *)
  if output_native_objects then
    let fn = Filename.dirname f ^"/"^ Nativecode.mod_uid_of_dirpath dir in
    Nativelib.compile_library ast fn

let get_used_load_paths () =
  String.Set.elements
    (List.fold_left (fun acc (root, m) -> String.Set.add
      (Filename.dirname (library_full_filename m)) acc)
       String.Set.empty !libraries_loaded_list)

let _ = Nativelib.get_load_paths := get_used_load_paths
