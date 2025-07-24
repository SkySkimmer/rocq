(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Context

module RelDecl = Rel.Declaration
open RelDecl

type aname = Name.t binder_annot
type term = constr

type key = int
type keys = key list

type state =
  { state_context : rel_context;
    state_subst : constr list;
  }

let newc s = s.state_context

let fresh_key s = List.length s.state_context

let init_state = { state_context = []; state_subst = [] }

let mk_state x y = { state_context = x; state_subst = y }

let weaken s c = Vars.substl s.state_subst c

let add_odecl s d =
  mk_state (RelDecl.map_constr (Vars.substl s.state_subst) d :: s.state_context)
    (mkRel 0 :: List.map (Vars.lift 1) s.state_subst)

let add_ovar (s : state) (an : aname) (ty : constr) : state =
  add_odecl s (LocalAssum (an, ty))

let add_old_var : state -> aname -> term -> (state * key -> 'a) -> 'a =
  fun s an ty cc ->
  let s' = add_ovar s an ty in
  cc (s', (fresh_key s))

let add_oletin (s : state) (an : aname) (db : term) (ty : term) : state =
  add_odecl s (LocalDef (an, db, ty))

let add_old_letin : state -> aname -> term -> term -> (state * key -> 'a) -> 'a =
  fun s an db ty cc ->
  let s' = add_oletin s  an db ty in
  cc (s', (fresh_key s))

let add_ocontext (s : state) (cxt : rel_context) : state =
  List.fold_right (fun d s -> add_odecl s d)
    cxt s


let add_fdecl s d =
  mk_state (d :: s.state_context)
    (List.map (Vars.lift 1) s.state_subst)

let add_fvar s na t = add_fdecl s (LocalAssum (na,t))

let add_fresh_var : state -> aname -> term -> (state * key -> 'a) -> 'a =
  fun s an ty cc ->
  let s' = add_fvar s an ty in
  cc (s', (fresh_key s))

let add_fletin (s : state) (an : aname) (db : term) (ty : term) : state =
  mk_state (LocalDef (an, db, ty) :: newc s)
    (List.map (Vars.lift 1) s.state_subst)


let add_fresh_letin : state -> aname -> term -> term -> (state * key -> _) -> _ =
  fun s an db ty cc ->
  let s' = add_fletin s an db ty in
  cc (s', (fresh_key s))

let add_fcontext (s : state) (cxt : rel_context) : state =
  List.fold_right (fun d s -> add_fdecl s d)
    cxt s


let subst_obind (s : state) (tm : term) : state =
  mk_state s.state_context
    (tm :: List.map (Vars.lift 1) s.state_subst)

(* 3. Substitute existing var / letin / context *)
let subst_old_bind : state -> term -> (state -> _) -> _ =
  fun s tm cc ->
  let s' = subst_obind s tm in
  cc s'

let subst_ocontext (s : state) (ltm : term list) : state =
  mk_state s.state_context
  (List.rev_append ltm (List.map (Vars.lift (List.length ltm)) s.state_subst))

let subst_old_context : state -> term list -> (state -> _) -> _ =
  fun s ltm cc ->
  let s' = subst_ocontext s ltm in
  cc s'

(* Get and check functions for the context

1. Access the context by ident
-----------------------------------------------------------------
- get_term   : ident -> state -> term
- geti_term  : list ident -> nat -> state -> term
- getij_term : list (list ident) -> nat -> nat -> state -> term
- get_terms  : list ident -> state -> list term
-----------------------------------------------------------------
- get_type   : ident -> state -> term
- geti_type  : list ident -> nat -> state -> term
- getij_type : list (list ident) -> nat -> nat -> state -> term
- get_types  : list ident -> state -> list term
-----------------------------------------------------------------
- get_aname   : ident -> state -> aname
- geti_aname  : list ident -> nat -> state -> aname
- getij_aname : list (list ident) -> nat -> nat -> state -> aname
- get_anames  : list ident -> state -> list aname
-----------------------------------------------------------------
- check_pos : ident -> nat -> state -> bool

2. Access the context by the position
-----------------------------------------------------------------
getp_name  : nat -> state -> ident
getp_aname : nat -> state -> aname
getp_body  : nat -> state -> option term
getp_type  : nat -> state -> term
check_id   : nat -> ident -> state -> bool
check_ids  : nat -> list ident -> state -> bool

3. Others
-----------------------------------------------------------------
- newc : state -> context
- reduce_lets : state -> term -> term
- reduce_except_lets :  global_env -> state -> term -> term
- reduce_full : global_env -> state -> term -> term

*)
let get_decl : state -> key -> rel_declaration =
  fun s k ->
  let n' = List.length s.state_context - k -1 in
  RelDecl.map_constr (Vars.lift n') (List.nth s.state_context n')


let getters f =
  let get_X : state -> key -> _ =
      fun s k -> f (List.length (newc s) - k -1) (get_decl s k)
  in

  let geti_X : state -> keys -> int -> _ =
      fun s ks pos_k -> get_X s (List.nth ks pos_k)
  in

  let getij_X : state -> keys list -> int -> int -> _ =
      fun s kss pos_k1 pos_k2 -> get_X s (List.nth (List.nth kss pos_k1) pos_k2)
  in

  let get_Xs : state -> keys -> _ list =
      fun s ks -> List.map (fun k -> get_X s k) ks
  in
  (get_X, geti_X, getij_X, get_Xs)

let get_sdecl_term : int -> rel_declaration -> term =
  fun n d ->
  match RelDecl.get_value d with
  | Some tm -> Vars.lift 1 tm
  | None -> mkRel n

let get_term, geti_term, getij_term, get_terms = getters get_sdecl_term

let get_sdecl_type : int -> rel_declaration -> term =
  fun _ d -> Vars.lift 1 (RelDecl.get_type d)

let get_type, geti_type, getij_type, get_types = getters get_sdecl_type

let get_sdecl_aname : int -> rel_declaration -> aname =
  fun _ cdecl -> RelDecl.get_annot cdecl

let get_aname, geti_aname, getij_aname, get_anames = getters get_sdecl_aname




(* 1.5 Check *)
let get_pos : state -> key -> int =
  fun s k -> List.length (newc s) - k - 1

let check_pos: state -> key -> int -> bool =
  fun s k read_pos -> Int.equal (List.length (newc s) -k -1) read_pos

(* Interface to create terms

  1. Functions for building inductive types
-----------------------------------------------------------------
- replace_ind {X} : kername -> state -> (state -> X) -> X
- make_ind : kername -> nat -> list ident -> list ident -> list ident -> state -> term
- make_cst : kername -> nat -> nat -> list ident -> list ident -> state -> term

  2. Keep and Make Let in
-----------------------------------------------------------------
- kp_tLetIn : aname -> term -> term -> state -> (ident -> state -> term) -> term
- mk_tLetIn : aname -> term -> term -> state -> (ident -> state -> term) -> term

  3. Keep and Make Binary binder(s)
--------------------------------------------------------------------------------
Context (binder : aname -> term -> term -> term)

- kp_binder : aname -> term -> option ident -> state -> (ident -> state -> term) -> term
- it_kp_binder : context -> option ident -> state -> (list ident -> state -> term) -> term
- closure_uparams : kername -> state -> (list ident -> state -> term) -> term
- closure_nuparams : kername -> state -> (list ident -> state -> term) -> term
- closure_params : kername -> state -> (list ident -> state -> term) -> term

- mk_binder : aname -> term -> option ident -> state -> (ident -> state -> term) -> term
- it_mk_binder : context -> option ident -> state -> (list ident -> state -> term) -> term
- closure_indices : kername -> nat -> state -> (list ident -> state -> term) -> term
- closure_binder {A} : option ident -> list A -> (naming : nat -> A -> aname) ->
    (typing : nat -> A -> state -> term) -> state -> (list ident -> state -> term) -> term

- kp_tProd / kp_tLambda / mk_tProd / mk_tLambda

  4. Make Fixpoint
--------------------------------------------------------------------------------
Context (kname : kername)
        (fty   : nat -> term)
        (frarg : nat -> nat)

- mk_tFix : nat -> state -> (list ident -> nat -> state -> term) -> term

End

- tFix_default_rarg : kername -> state -> nat -> nat

  5. Make Match
-----------------------------------------------------------------
Context (kname : kername) (pos_indb : nat) (indb : one_inductive_body)
        (key_uparams key_nuparams : list ident)
        (mk_case_pred : list ident -> ident -> state -> term)

- mk_tCase : term -> state -> (nat -> list ident -> list ident -> list ident -> state -> term) -> term

*)


let (let*) x f = x f

(* 1. Keep and Make Binary Binders *)
let kp_binder binder : state -> aname -> term -> (state -> key -> term) -> term =
  fun s an ty cc ->
  let ty' = weaken s ty in
  let* (s', key_bind) = add_old_var s an ty in
  binder (an, ty', (cc s' key_bind))

let kp_tProd = kp_binder mkProd
let kp_tLambda = kp_binder mkLambda

let mk_binder binder : state -> aname -> term -> (state -> key -> term) -> term =
  fun s an ty cc ->
    let* (s, key_mk) = add_fresh_var s an ty in
    binder (an, ty, (cc s key_mk))

let mk_tProd = mk_binder mkProd
let mk_tLambda = mk_binder mkLambda

(* 2. Keep and Make Let in *)
let kp_tLetIn : state -> aname -> term -> term -> (state -> key -> term) -> term =
  fun s an db ty cc ->
  let db' = weaken s db in
  let ty' = weaken s ty in
  let* (s', key_let) = add_old_letin s an db ty in
  mkLetIn (an, db', ty', (cc s' key_let))

let mk_tLetIn : state -> aname -> term -> term -> (state * key -> term) -> term =
  fun s an db ty cc ->
  let* (s, key_let) = add_fresh_letin s an db ty in
  mkLetIn (an, db, ty, (cc (s, key_let)))

(* 3. Inductive Terms *)

let unsafe_instance = UVars.Instance.empty

(* Builds: Ind A1 ... An B0 ... Bm i1 ... il *)
let make_ind : state -> MutInd.t -> int -> keys -> keys -> keys -> term =
  fun s kname pos_indb key_uparams key_nuparams key_indices ->
  Term.applist (mkIndU ((kname, pos_indb), unsafe_instance),
                (List.concat [get_terms s key_uparams;
                              get_terms s key_nuparams;
                              get_terms s key_indices]))

let make_indt : state -> MutInd.t -> int -> keys -> term list -> term list -> term =
  fun s kname pos_indb key_uparams nuparams indices ->
  Term.applist (mkIndU ((kname, pos_indb), unsafe_instance),
                (List.concat [get_terms s key_uparams; nuparams; indices]))


(* Builds: Cst A1 ... An B0 ... Bm *)
let make_cst : state -> MutInd.t -> int -> int -> keys -> keys -> term =
  fun s kname pos_indb pos_ctor key_uparams key_nuparams ->
  Term.applist (mkConstructU (((kname, pos_indb), pos_ctor), unsafe_instance),
                (List.concat [get_terms s key_uparams; get_terms s key_nuparams]))

let fold_right_state tp l s t =
  let rec aux n ids1 l s t =
    match l with
    | [] -> t s (List.rev ids1)
    | a :: l -> tp n a s (fun s id1 -> aux (succ n) (id1 :: ids1) l s t)
  in
  aux 0 [] l s t

let fold_left_state tp l s t =
  fold_right_state tp (List.rev l) s t

let fold_right_state_opt {A B X state} (n : nat) (s : state) (l : list A)
  (tp :  state -> nat -> A ->(state -> iter_T n (list X) B) -> B) (t : state -> iter_T n (list X) B) : B :=
  let fix aux (s : state) (pos : nat) (ids : Vector.t (list X) n) (l : list A) {struct l} : B :=
    match l with
    | [] => iter_X (Vector.map (@List.rev _) ids) (t s)
    | a :: l => tp s pos a (fun s => X_iter (fun x => aux s (S pos) (Vector.map2 (@List.app _) x ids) l))
    end
  in
  aux s 0 (Vector.const [] n) l

let fold_right_state_opt tp l s t =
  let rec aux n ids1 l s t =
    match l with
    | [] -> t s (List.rev ids1)
    | a :: l -> tp a s (fun s id1 -> aux (succ n) (List.append id1 ids1) l s t)
  in
  aux 0 [] l s t

let fold_left_state_opt tp l s t =
  fold_right_state_opt tp (List.rev l) s t

let aux
    (read_letin : state -> aname -> term -> term ->
     (state * key -> 'x) -> 'x)
    (read_var   : state -> aname -> term ->
     (state * key -> 'x) -> 'x) =
  let read_by_decl
      s cxt
      ccletin ccvar
    =
    fold_left_state_opt (fun decl s decl cc ->
        let an = RelDecl.get_annot decl in
        let ty = RelDecl.get_type decl in
        match RelDecl.get_value decl with
        | Some db -> let* (s, key_letin) = read_letin s an db ty in
          ccletin s key_letin cc
        | None    -> let* (s, key_var) = read_var s an ty in
          ccvar s key_var cc)
      cxt s
  in

  let cc_triv : state -> int -> key -> (state -> keys -> 'x) -> 'x =
    fun s pos k cc -> cc s [k]
  in

  let read_context : state -> rel_context -> (state -> keys -> 'x) -> 'x =
    fun s x cxt -> read_by_decl 1 s cxt cc_triv cc_triv
  in
  read_context
