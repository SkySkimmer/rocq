(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Interpretation of search commands *)

open CErrors
open Names
open Util
open Pp
open Printer
open Search
open Vernacexpr
open Goptions

let open_or_global_module qid =
  try Nametab.full_name_open_mod qid
  with Not_found ->
    try Nametab.full_name_module qid
    with Not_found ->
      user_err ?loc:qid.CAst.loc
       (str "Module/Section " ++ Ppconstr.pr_qualid qid ++ str " not found.")

(*
let global_module qid =
    user_err ?loc:qid.CAst.loc
     (str "Module/Section " ++ Ppconstr.pr_qualid qid ++ str " not found.")
*)
let interp_search_restriction = function
  | SearchOutside l ->
      SearchOutside (List.map open_or_global_module l)
  | SearchInside l ->
      SearchInside (List.map open_or_global_module l)

let kind_searcher env = Decls.(function
  (* Kinds referring to the keyword introducing the object *)
  | IsAssumption _
  | IsDefinition (Definition | Example | Fixpoint | CoFixpoint | Method | StructureComponent | Let | LetContext)
  | IsProof _
  | IsPrimitive
  | IsSymbol as k -> Inl k
  (* Kinds referring to the status of the object *)
  | IsDefinition (Coercion | SubClass | IdentityCoercion as k') ->
    let coercions = Coercionops.coercions () in
    Inr (fun gr -> List.exists (fun c -> Environ.QGlobRef.equal env c.Coercionops.coe_value gr &&
                                      (k' <> SubClass && k' <> IdentityCoercion || c.Coercionops.coe_is_identity)) coercions)
  | IsDefinition CanonicalStructure ->
    let canonproj = Structures.CSTable.entries () in
    Inr (fun gr -> List.exists (fun c -> Environ.QGlobRef.equal env c.Structures.CSTable.solution gr) canonproj)
  | IsDefinition Scheme ->
    let schemes = DeclareScheme.all_schemes () in
    let schemes = lazy begin
      Indmap.fold (fun _ schemes acc ->
          CString.Map.fold (fun _ c acc -> Cset.add c acc) schemes acc)
        schemes Cset.empty
    end
    in
    Inr (function
        | ConstRef c -> Cset.mem c (Lazy.force schemes)
        | _ -> false)
  | IsDefinition Instance ->
    let instances = Typeclasses.all_instances () in
    Inr (fun gr -> List.exists (fun c -> Environ.QGlobRef.equal env c.Typeclasses.is_impl gr) instances))

let interp_constr_pattern env sigma ?(expected_type=Pretyping.WithoutTypeConstraint) c =
  let c = Constrintern.intern_gen expected_type ~pattern_mode:true env sigma c in
  let flags = { Pretyping.no_classes_no_fail_inference_flags with expand_evars = false } in
  let sigma, c = Pretyping.understand_tcc ~flags env sigma ~expected_type c in
  (* FIXME: it is necessary to be unsafe here because of the way we handle
     evars in the pretyper. Sometimes they get solved eagerly. *)
  Patternops.legacy_bad_pattern_of_constr env sigma c

let interp_search_item env sigma =
  function
  | SearchSubPattern ((where,head),pat) ->
      let expected_type = Pretyping.(if head then IsType else WithoutTypeConstraint) in
      let pat =
        try interp_constr_pattern env sigma ~expected_type pat
        with e when CErrors.noncritical e ->
          (* We cannot ensure (yet?) that a typable pattern will
             actually be typed, consider e.g. (forall A, A -> A /\ A)
             which fails, not seeing that A can be Prop; so we use an
             untyped pattern as a fallback (i.e w/o no insertion of
             coercions, no compilation of pattern-matching) *)
          snd (Constrintern.interp_constr_pattern env sigma ~as_type:head pat) in
      GlobSearchSubPattern (where,head,pat)
  | SearchString ((Anywhere,false),s,None)
      when Id.is_valid_ident_part s && String.equal (String.drop_simple_quotes s) s ->
      GlobSearchString s
  | SearchString ((where,head),s,sc) ->
      let sc = Option.map snd sc in
      let ref =
        Notation.interp_notation_as_global_reference
          ~head:false (fun _ -> true) s sc in
      GlobSearchSubPattern (where,head,Pattern.PRef ref)
  | SearchKind k ->
     match kind_searcher env k with
     | Inl k -> GlobSearchKind k
     | Inr f -> GlobSearchFilter f

let rec interp_search_request env sigma = function
  | b, SearchLiteral i -> b, GlobSearchLiteral (interp_search_item env sigma i)
  | b, SearchDisjConj l -> b, GlobSearchDisjConj (List.map (List.map (interp_search_request env sigma)) l)

(* 05f22a5d6d5b8e3e80f1a37321708ce401834430 introduced the
   `search_output_name_only` option to avoid excessive printing when
   searching.

   The motivation was to make search usable for IDE completion,
   however, it is still too slow due to the non-indexed nature of the
   underlying search mechanism.

   In the future we should deprecate the option and provide a fast,
   indexed name-searching interface.
*)
let search_output_name_only = ref false

let () =
  declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Search";"Output";"Name";"Only"];
      optread  = (fun () -> !search_output_name_only);
      optwrite = (:=) search_output_name_only }

let interp_search env sigma s r =
  let r = interp_search_restriction r in
  let get_pattern c = snd (Constrintern.interp_constr_pattern env sigma c) in
  let warnlist = ref [] in
  let pr_search ref kind env sigma c =
    let pr = pr_global ref in
    let pp = if !search_output_name_only
      then pr
      else begin
        let open Impargs in
        let impls = implicits_of_global ref in
        let impargs = select_stronger_impargs impls in
        let impargs = List.map binding_kind_of_status impargs in
        if List.length impls > 1 ||
           List.exists Glob_term.(function Explicit -> false | MaxImplicit | NonMaxImplicit -> true)
             (List.skipn_at_best (Termops.nb_prod_modulo_zeta sigma (EConstr.of_constr c)) impargs)
          then warnlist := pr :: !warnlist;
        let pc = pr_ltype_env env sigma ~impargs c in
        hov 2 (pr ++ str":" ++ spc () ++ pc)
      end
    in Feedback.msg_notice pp
  in
  (match s with
  | SearchPattern c ->
      (Search.search_pattern env sigma (get_pattern c) r |> Search.prioritize_search) pr_search
  | SearchRewrite c ->
      (Search.search_rewrite env sigma (get_pattern c) r |> Search.prioritize_search) pr_search
  | Search sl ->
      (Search.search env sigma (List.map (interp_search_request env Evd.(from_env env)) sl) r |>
       Search.prioritize_search) pr_search);
  if !warnlist <> [] then
  Feedback.msg_notice (str "(" ++
    hov 0 (strbrk "use \"About\" for full details on the implicit arguments of " ++
           pr_enum (fun x -> x) !warnlist ++ str ")"))
