(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Constr
open Context
open CoqSharingAnalyser

(** Constr annotated with graph structure info *)
module GConstr : sig
  type gkind

  type t = private {
    self : constr;
    uid : int;
    mutable refcount : int;
    kind : gkind; (* keeping gkind abstract makes the automatic ocamldebug printer more readable *)
  }

  val kind : t -> (t,t,Sorts.t,UVars.Instance.t,Sorts.relevance) kind_of_term

  val of_constr : constr -> t

end = struct
  type t = {
    self : constr;
    uid : int;
    mutable refcount : int;
    kind : gkind;
  }
  and gkind = (t,t,Sorts.t,UVars.Instance.t,Sorts.relevance) kind_of_term

  let kind x = x.kind

  let dbg_sharing = CDebug.create ~name:"constrsharing" ()

  (* WARNING very slow *)
  let debug_check c info =
    let info = ref info in
    let seen = ref [] in
    let cnt = ref 0 in
    let rec aux c =
      let this = SharingAnalyser.ref_step info in
      match this, List.find_opt (fun (c',_) -> c == c') !seen with
      | SharingAnalyser.Seen i, Some (_,j) ->
        if not (Int.equal i j) then
          CErrors.anomaly Pp.(str "check-hconstr-sharing mismatch: got " ++ int i ++
                              str " but should be " ++ int j)
      | SharingAnalyser.Fresh i, None ->
        assert (Int.equal i !cnt);
        seen := (c,i) :: !seen;
        incr cnt;
        Constr.iter aux c
      | _ -> assert false
    in
    let () = aux c in
    assert (SharingAnalyser.is_done !info);
    ()

  let check_sharing, _ = CDebug.create_full ~name:"slow-check-hconstr-sharing" ()

  let of_constr c =
    let open SharingAnalyser in
    let info = NewProfile.profile "sharingAnalyser" (fun () ->
        analyse constr_descr (Obj.repr c))
        ()
    in
    (* can be printed in ocamldebug *)
    let _debug = mk_debug info c in
    let () =
      dbg_sharing Pp.(fun () ->
          let l = SharingAnalyser.to_list info in
          let (fresh,shared) = List.fold_left (fun (fresh,shared) -> function
              | SharingAnalyser.Fresh _ -> fresh+1, shared
              | SharingAnalyser.Seen _ -> fresh, shared+1)
              (0,0)
              l
          in
          str "fresh = " ++ int fresh ++ pr_comma() ++ str "shared = " ++ int shared
        )
    in
    let () = if CDebug.get_flag check_sharing then debug_check c info in

    let info = ref info in
    let map = ref Int.Map.empty in
    let rec of_constr c =
      match ref_step info with
      | Seen n -> begin match Int.Map.find_opt n !map with
          | None -> assert false
          | Some v ->
            assert (v.self == c);
            v.refcount <- v.refcount + 1;
            v
        end
      | Fresh n ->
        let k = of_kind (Constr.kind c) in
        let v = { self = c; uid = n; refcount = 1; kind = k } in
        map := Int.Map.add n v !map;
        v

    and of_kind = function
      | Rel _ | Var _ | Meta _ | Sort _
      | Const _ | Ind _ | Construct _
      | Int _ | Float _ | String _ as k ->
        k
      | Evar (ev,l) -> Evar (ev,SList.Skip.map of_constr l)
      | Cast (c1,k,c2) ->
        let c1 = of_constr c1 in
        let c2 = of_constr c2 in
        Cast (c1,k,c2)
      | Prod (na,c1,c2) ->
        let c1 = of_constr c1 in
        let c2 = of_constr c2 in
        Prod (na,c1,c2)
      | Lambda (na,c1,c2) ->
        let c1 = of_constr c1 in
        let c2 = of_constr c2 in
        Lambda (na,c1,c2)
      | LetIn (na,c1,c2,c3) ->
        let c1 = of_constr c1 in
        let c2 = of_constr c2 in
        let c3 = of_constr c3 in
        LetIn (na,c1,c2,c3)
      | App (h,args) ->
        let h = of_constr h in
        let args = Array.map of_constr args in
        App (h,args)
      | Case (ci,u,pms,(p,r),iv,c,brs) ->
        let pms = Array.map of_constr pms in
        let p = of_under_ctx p in
        let iv = match iv with
          | NoInvert -> NoInvert
          | CaseInvert iv ->
            CaseInvert {indices=Array.map of_constr iv.indices}
        in
        let c = of_constr c in
        let brs = Array.map of_under_ctx brs in
        Case (ci,u,pms,(p,r),iv,c,brs)
      | Fix (tl,vs) -> Fix (tl, of_recdef vs)
      | CoFix (tl,vs) -> CoFix (tl, of_recdef vs)
      | Proj (p,r,c) -> Proj (p,r,of_constr c)
      | Array (u,elems,def,ty) ->
        let elems = Array.map of_constr elems in
        let def = of_constr def in
        let ty = of_constr ty in
        Array (u,elems,def,ty)

    and of_under_ctx (nas,c) = (nas, of_constr c)

    and of_recdef (nas,tys,bdys) =
      let tys = Array.map of_constr tys in
      let bdys = Array.map of_constr bdys in
      (nas, tys, bdys)
    in
    NewProfile.profile "HConstr.GConstr.of_constr" (fun () ->
        of_constr c)
      ()
end

(* TODO explain how this works *)

module Self = struct

type t = {
  self : constr;
  kind : (t,t,Sorts.t,UVars.Instance.t,Sorts.relevance) kind_of_term;
  isRel : int (* 0 -> not a rel, otherwise unique identifier of that binder *);
  unbound_rels : int SList.t;
  hash : int;
  mutable refcount : int;
}

let equal a b =
  a.isRel == b.isRel
  && hasheq_kind a.kind b.kind

let hash x = x.hash

end

include Self

let raw_equal a ~isRel ~kind =
  a.isRel == isRel
  && hasheq_kind a.kind kind

let self x = x.self

let refcount x = x.refcount

module Tbl = struct
  type key = t

  (* The API looks like Hashtbl but implemented using Int.Map ref.

     We don't use Hashtbl for 2 reasons:
     - to provide the pre-hashconsing leaf lookup (not sure why it's so fast but it seems to be)
       (although note we could do this with Hashtbl by using something like
       [type key = Real of t | Fake of int (* hash *) * (t -> bool)],
       equality between [Real] and [Fake] uses the predicate in [Fake],
       wrap [add] so that we only add [Real] keys,
       then [raw_find] is [Hashtbl.find_opt] using [Fake].)

     - for unclear reasons Int.Map ref is dramatically faster on an artificial example
       (balanced binary tree whose leaves are all different primitive ints,
        such that there is no sharing).
       It is a bit slower in the real world.
       It seems that hashtbl produces overly large buckets which then need to be linearly scanned.
       hconsing doesn't seem to have this problem,
       perhaps because of differences between hashtbl and our hashset implementation. *)
  type 'a t = (key * 'a) list Int.Map.t ref

  let create _ = ref Int.Map.empty

  let add tbl key v =
    tbl := Int.Map.update key.hash (function
        | None -> Some [(key,v)]
        | Some l -> Some ((key,v)::l))
        !tbl

  let raw_find tbl h p =
    match Int.Map.find_opt h !tbl with
    | None -> None
    | Some l -> List.find_map (fun (k,v) -> if p k then Some v else None) l

  let find_opt tbl key =
    match Int.Map.find_opt key.hash !tbl with
    | None -> None
    | Some l ->
      List.find_map (fun (k',v) ->
          if equal key k' then Some v else None)
        l

  type stats = {
    hashes : int;
    bindings : int;
    most_collisions : int;
  }

  let empty_stats = {
    hashes = 0;
    bindings = 0;
    most_collisions = 0;
  }

  let stats tbl =
    Int.Map.fold (fun _ l acc ->
        let len = List.length l in
        {
          hashes = acc.hashes + 1;
          bindings = acc.bindings + len;
          most_collisions = max acc.most_collisions len;
        }
      )
      !tbl
      empty_stats

end

module UBRelKey = struct
  type t = int SList.t
  let compare x y = SList.compare Int.compare x y
end

module UBRelMap = Map.Make(UBRelKey)

type local_env = {
  (* only used for globals, rel context is not correct *)
  globals : Environ.env;
  (* unique identifiers for each binder crossed *)
  rels : int Range.t;
  (* global counter *)
  cnt : int ref;
  (* how many unknown_rel we have seen *)
  unknown_cnt : int ref;
  assum_uids : int Tbl.t;
  (* the surrounding table is for the body, the inner table for the type *)
  letin_uids : int Tbl.t Tbl.t;
  (* already seen terms according to sharing info
     we keep the [analysis] because if the ub rels are different we need to restart *)
  shared_seen : (Constr.t * t UBRelMap.t) Int.Map.t ref;
}

let empty_env env = {
  globals = env;
  rels = Range.empty;
  cnt = ref 0;
  unknown_cnt = ref 0;
  assum_uids = Tbl.create 47;
  letin_uids = Tbl.create 47;
  shared_seen = ref Int.Map.empty;
}

(* still used in fixpoint *)
let push_unknown_rel env =
  incr env.cnt;
  incr env.unknown_cnt;
  { env with rels = Range.cons !(env.cnt) env.rels }

let push_assum t env =
  let uid = match Tbl.find_opt env.assum_uids t with
  | Some uid -> uid
  | None ->
    incr env.cnt;
    let uid = !(env.cnt) in
    Tbl.add env.assum_uids t uid;
    uid
  in
  { env with rels = Range.cons uid env.rels }

let push_rec ts env =
  (* handling the lifting for mutual fixpoints doesn't seem worth the effort *)
  Array.fold_left_i (fun i env t ->
      if i = 0 then push_assum t env
      else push_unknown_rel env)
    env
    ts

let push_letin ~body ~typ env =
  let uid = match Tbl.find_opt env.letin_uids body with
    | Some tbl -> begin match Tbl.find_opt tbl typ with
        | Some uid -> uid
        | None ->
          incr env.cnt;
          let uid = !(env.cnt) in
          Tbl.add tbl typ uid;
          uid
      end
    | None ->
      incr env.cnt;
      let uid = !(env.cnt) in
      let tbl = Tbl.create 3 in
      Tbl.add tbl typ uid;
      Tbl.add env.letin_uids body tbl;
      uid
  in
  { env with rels = Range.cons uid env.rels }

module RelDecl = Context.Rel.Declaration

let push_decl d env = match d with
  | RelDecl.LocalAssum (_,t) -> push_assum t env
  | RelDecl.LocalDef (_,body,typ) -> push_letin ~body ~typ env

let hash_annot = hash_annot Name.hash

let hash_array hashf a = Array.fold_left (fun hash x -> Hashset.Combine.combine hash (hashf x)) 0 a

let hash_kind = let open Hashset.Combine in function
  | Var i -> combinesmall 1 (Id.hash i)
  | Sort s -> combinesmall 2 (Sorts.hash s)
  | Cast (c,k,t) -> combinesmall 3 (combine3 c.hash (hash_cast_kind k) t.hash)
  | Prod (na,t,c) -> combinesmall 4 (combine3 (hash_annot na) t.hash c.hash)
  | Lambda (na,t,c) -> combinesmall 5 (combine3 (hash_annot na) t.hash c.hash)
  | LetIn (na,b,t,c) -> combinesmall 6 (combine4 (hash_annot na) b.hash t.hash c.hash)
  | App (h,args) -> combinesmall 7 (Array.fold_left (fun hash c -> combine hash c.hash) h.hash args)
  | Evar _ -> assert false
  | Const (c,u) -> combinesmall 9 (combine (Constant.SyntacticOrd.hash c) (UVars.Instance.hash u))
  | Ind (ind,u) -> combinesmall 10 (combine (Ind.SyntacticOrd.hash ind) (UVars.Instance.hash u))
  | Construct (c,u) -> combinesmall 11 (combine (Construct.SyntacticOrd.hash c) (UVars.Instance.hash u))
  | Case (_,u,pms,(p,_),_,c,bl) ->
    let hash_ctx (bnd,c) =
      Array.fold_left (fun hash na -> combine (hash_annot na) hash) c.hash bnd
    in
    let hpms = hash_array hash pms in
    let hbl = hash_array hash_ctx bl in
    let h = combine5 (UVars.Instance.hash u)
        c.hash hpms (hash_ctx p) hbl
    in
    combinesmall 12 h
  | Fix (_,(lna,tl,bl)) ->
    combinesmall 13 (combine3 (hash_array hash_annot lna) (hash_array hash tl) (hash_array hash bl))
  | CoFix (_,(lna,tl,bl)) ->
    combinesmall 14 (combine3 (hash_array hash_annot lna) (hash_array hash tl) (hash_array hash bl))
  | Meta _ -> assert false
  | Rel n -> combinesmall 16 n
  | Proj (p,_,c) -> combinesmall 17 (combine (Projection.SyntacticOrd.hash p) c.hash)
  | Int i -> combinesmall 18 (Uint63.hash i)
  | Float f -> combinesmall 19 (Float64.hash f)
  | String s -> combinesmall 20 (Pstring.hash s)
  | Array (u,t,def,ty) -> combinesmall 21 (combine4 (UVars.Instance.hash u) (hash_array hash t) def.hash ty.hash)

let kind_to_constr = function
  | Rel n -> mkRel n
  | Var i -> mkVar i
  | Meta _ | Evar _ -> assert false
  | Sort s -> mkSort s
  | Cast (c,k,t) -> mkCast (c.self,k,t.self)
  | Prod (na,t,c) -> mkProd (na,t.self,c.self)
  | Lambda (na,t,c) -> mkLambda (na,t.self,c.self)
  | LetIn (na,b,t,c) -> mkLetIn (na,b.self,t.self,c.self)
  | App (h,args) -> mkApp (h.self, Array.map self args)
  | Const cu -> mkConstU cu
  | Ind iu -> mkIndU iu
  | Construct cu -> mkConstructU cu
  | Case (ci,u,pms,(p,r),iv,c,bl) ->
    let to_ctx (bnd,c) = bnd, c.self in
    let iv = match iv with
      | NoInvert -> NoInvert
      | CaseInvert x -> CaseInvert {indices=Array.map self x.indices}
    in
    mkCase (ci,u,Array.map self pms,(to_ctx p,r),iv,c.self,Array.map to_ctx bl)
  | Fix (ln,(lna,tl,bl)) ->
    mkFix (ln,(lna,Array.map self tl,Array.map self bl))
  | CoFix (ln,(lna,tl,bl)) ->
    mkCoFix (ln,(lna,Array.map self tl,Array.map self bl))
  | Proj (p,r,c) -> mkProj (p,r,c.self)
  | Int i -> mkInt i
  | Float f -> mkFloat f
  | String s -> mkString s
  | Array (u,t,def,ty) -> mkArray (u,Array.map self t,def.self,ty.self)

let hcons_inplace f a = Array.iteri (fun i x -> Array.unsafe_set a i (f x)) a

let rec pop_unbound_rels n l =
  if n = 0 then l else match l with
    | SList.Nil -> l
    | SList.Cons (_,tl) -> pop_unbound_rels (n-1) tl
    | SList.Default (m,tl) ->
      if n < m then SList.defaultn (m-n) tl
      else pop_unbound_rels (n-m) tl

let rec combine_unbound_rels l1 l2 =
  if l1 == l2 then l1 else match l1, l2 with
  | SList.Nil, _ -> l2
  | _, SList.Nil -> l1
  | SList.Cons (x,tl1), SList.Cons (y,tl2) ->
    assert (Int.equal x y);
    let tl = combine_unbound_rels tl1 tl2 in
    if tl == tl1 then l1 else if tl == tl2 then l2 else SList.cons x tl
  | SList.Cons (x,tl1), SList.Default (n,tl2) ->
    let tl = combine_unbound_rels tl1 (SList.defaultn (n-1) tl2) in
    if tl == tl1 then l1 else SList.cons x tl
  | SList.Default (n,tl1), SList.Cons (y,tl2) ->
    let tl = combine_unbound_rels (SList.defaultn (n-1) tl1) tl2 in
    if tl == tl2 then l2 else SList.cons y tl
  | SList.Default (n,tl1), SList.Default (m,tl2) ->
    let n, m, tl1, tl2, l1 = if n < m then n, m, tl1, tl2, l1 else m, n, tl2, tl1, l2 in
    let tl = combine_unbound_rels tl1 (SList.defaultn (m-n) tl2) in
    if tl == tl1 then l1 else SList.defaultn n tl

let kind_unbound_rels = function
  | Rel _ -> assert false
  | Var _ | Sort _ | Const _ | Construct _ | Ind _ | Int _ | Float _ | String _ -> SList.empty
  | Meta _ | Evar _ -> assert false
  | Cast (c1,_,c2) -> combine_unbound_rels c1.unbound_rels c2.unbound_rels
  | Prod (_,c1,c2) | Lambda (_,c1,c2) ->
    combine_unbound_rels c1.unbound_rels (pop_unbound_rels 1 c2.unbound_rels)
  | LetIn (_,c1,c2,c3) ->
    let rels = combine_unbound_rels c1.unbound_rels c2.unbound_rels in
    combine_unbound_rels rels (pop_unbound_rels 1 c3.unbound_rels)
  | App (h,args) ->
    Array.fold_left (fun rels arg -> combine_unbound_rels rels arg.unbound_rels) h.unbound_rels args
  | Case (_,_,pms,(p,_),iv,c,bl) ->
    let fold_ctx rels (bnd,c) =
      combine_unbound_rels rels (pop_unbound_rels (Array.length bnd) c.unbound_rels)
    in
    let rels = c.unbound_rels in
    let rels = match iv with
      | NoInvert -> rels
      | CaseInvert {indices} ->
        Array.fold_left (fun rels i -> combine_unbound_rels rels i.unbound_rels) rels indices
    in
    let rels = Array.fold_left (fun rels pm -> combine_unbound_rels rels pm.unbound_rels) rels pms in
    let rels = fold_ctx rels p in
    let rels = Array.fold_left fold_ctx rels bl in
    rels
  | Fix (_,recdef) | CoFix (_,recdef) ->
    let nas,tys,bdys = recdef in
    let rels = Array.fold_left (fun rels ty ->
        combine_unbound_rels rels ty.unbound_rels)
        SList.empty
        tys
    in
    Array.fold_left (fun rels bdy ->
        combine_unbound_rels rels (pop_unbound_rels (Array.length nas) bdy.unbound_rels))
      rels
      bdys
  | Proj (_,_,c) -> c.unbound_rels
  | Array (_,elems,def,ty) ->
    let rels = combine_unbound_rels def.unbound_rels ty.unbound_rels in
    Array.fold_left (fun rels elem -> combine_unbound_rels rels elem.unbound_rels) rels elems

let of_kind_nohashcons = function
  | App (c, [||]) -> c
  | kind ->
  let self = kind_to_constr kind in
  let hash = hash_kind kind in
  let () = match kind with
    | Rel _ -> assert false
    | _ -> ()
  in
  let unbound_rels = kind_unbound_rels kind in
  { self; kind; hash; isRel = 0; unbound_rels; refcount = 1 }

(* We can call use GConstr or directly Constr to produce a HConstr.t.
   The ability to avoid GConstr is useful for
   - Case binders where we only get constrs for the context types but still have to compute their binder uids
   - runtimes which can't use the SharingAnalyser C code (eg javascript)
   - if we want to have a paranoid mode which doesn't use GConstr for safety
     (although the asserts in GConstr.of_constr should be enough to prevent inconsistencies
      even if SharingAnalyser returns garbage)
*)
type _ gen_constr_tag =
  | ConstrTag : Constr.t gen_constr_tag
  | GConstrTag : GConstr.t gen_constr_tag

let gen_kind (type t) (tag:t gen_constr_tag) (c:t)
  : (t,t,Sorts.t,UVars.Instance.t,Sorts.relevance) kind_of_term
  = match tag with
  | ConstrTag -> Constr.kind c
  | GConstrTag -> GConstr.kind c

let gen_self (type t) (tag:t gen_constr_tag) (c:t) : Constr.t =
  match tag with
  | ConstrTag -> c
  | GConstrTag -> c.GConstr.self

let eq_leaf tag c c' = match gen_kind tag c, c'.kind with
  | Var i, Var i' -> Id.equal i i'
  | Const (c,u), Const (c',u') -> Constant.SyntacticOrd.equal c c' && UVars.Instance.equal u u'
  | Ind (i,u), Ind (i',u') -> Ind.SyntacticOrd.equal i i' && UVars.Instance.equal u u'
  | Construct (c,u), Construct (c',u') -> Construct.SyntacticOrd.equal c c' && UVars.Instance.equal u u'
  | _ -> false

let nonrel_leaf tbl tag c = match gen_kind tag c with
  | Rel _ -> None
  | Var _ | Const _ | Ind _ | Construct _ as k ->
    let h = hash_kind k in
    Tbl.raw_find tbl h (fun c' -> eq_leaf tag c c')
  | _ -> None

(* v tells which rels are bound *)
let ubrels_from_env (type a) local_env (v:a SList.t) =
  let rec aux local_env rels = match rels with
    | SList.Nil -> SList.empty
    | SList.Cons (_,tl) ->
      SList.cons (Range.hd local_env)
        (aux (Range.tl local_env) tl)
    | SList.Default (n,tl) ->
      SList.defaultn n (aux (Range.skipn n local_env) tl)
  in
  aux local_env.rels v

type sharing_info =
  | Fresh of int
  | RelsDiffer of int * UBRelKey.t
  | Seen of t

let sharing_info (type t) local_env (tag:t gen_constr_tag) (c:t) =
  match tag with
  | ConstrTag -> None
  | GConstrTag ->
    if c.refcount = 1 then None
    else match Int.Map.find_opt c.uid !(local_env.shared_seen) with
      | None -> Some (Fresh c.uid)
      | Some (self, results) ->
        assert (self == c.self);
        let key =
          let key', _ = UBRelMap.choose results in
          ubrels_from_env local_env key'
        in
        match UBRelMap.find_opt key results with
        | None -> Some (RelsDiffer (c.uid, key))
        | Some v -> Some (Seen v)

let steps = ref 0

let rec of_constr : 't. _ -> _ -> 't gen_constr_tag -> 't -> _
  = fun (type t) tbl local_env (tag:t gen_constr_tag) (c:t) ->
  incr steps;
  match sharing_info local_env tag c with
  | None -> of_constr_fresh tbl local_env ~unbound_rels:None tag c
  | Some (Fresh uid) ->
    let v = of_constr_fresh tbl local_env ~unbound_rels:None tag c in
    let () =
      local_env.shared_seen :=
        Int.Map.add uid
          (* add [c] NOT [v.self] otherwise we will get false positive mismatch errors *)
          (gen_self tag c, UBRelMap.singleton v.unbound_rels v)
          !(local_env.shared_seen)
    in
    v
  | Some (RelsDiffer (uid, key)) ->
    let v = of_constr_fresh tbl local_env ~unbound_rels:(Some key) tag c in
    let () =
      local_env.shared_seen :=
        Int.Map.update uid
          (function
            | None -> assert false
            | Some (c,m) -> Some (c, UBRelMap.add v.unbound_rels v m))
          !(local_env.shared_seen)
    in
    v
  | Some (Seen v) -> v.refcount <- v.refcount + 1; v

and of_constr_fresh : 't. _ -> _ -> unbound_rels:_ -> 't gen_constr_tag -> 't -> _
    = fun (type t) tbl local_env ~unbound_rels (tag:t gen_constr_tag) (c:t) ->
  match nonrel_leaf tbl tag c with
  | Some v -> v
  | None ->
    let kind = of_constr_aux tbl local_env tag c in
    let hash = hash_kind kind in
    let isRel, hash = match kind with
      | Rel n ->
        let uid = Range.get local_env.rels (n-1) in
        assert (uid <> 0);
        uid, Hashset.Combine.combine uid hash
      | _ -> 0, hash
    in
    match Tbl.raw_find tbl hash (fun c' -> raw_equal c' ~isRel ~kind) with
    | Some c' -> c'.refcount <- c'.refcount + 1; c'
    | None ->
      let unbound_rels = match unbound_rels with
        | Some v -> v
        | None -> match kind with
          | Rel n -> SList.defaultn (n-1) (SList.cons isRel SList.empty)
          | _ -> kind_unbound_rels kind
      in
      let c =
        let self = kind_to_constr kind in
        let self = if hasheq_kind (Constr.kind self) (Constr.kind (gen_self tag c))
          then gen_self tag c
          else self
        in
        { self; kind; hash; isRel; unbound_rels; refcount = 1 }
      in
      Tbl.add tbl c c; c

and of_constr_aux : 't. _ -> _ -> 't gen_constr_tag -> 't -> _
    = fun (type t) tbl local_env (tag:t gen_constr_tag) (orig:t) ->
  match gen_kind tag orig with
  | Var i ->
    let i = Id.hcons i in
    Var i
  | Rel _ as t -> t
  | Sort s ->
    let s = Sorts.hcons s in
    Sort s
  | Cast (c,k,t) ->
    let c = of_constr tbl local_env tag c in
    let t = of_constr tbl local_env tag t in
    Cast (c, k, t)
  | Prod (na,t,c) ->
    let na = hcons_annot na in
    let t = of_constr tbl local_env tag t in
    let c = of_constr tbl (push_assum t local_env) tag c in
    Prod (na, t, c)
  | Lambda (na, t, c) ->
    let na = hcons_annot na in
    let t = of_constr tbl local_env tag t in
    let c = of_constr tbl (push_assum t local_env) tag c in
    Lambda (na,t,c)
  | LetIn (na,b,t,c) ->
    let na = hcons_annot na in
    let b = of_constr tbl local_env tag b in
    let t = of_constr tbl local_env tag t in
    let c = of_constr tbl (push_letin ~body:b ~typ:t local_env) tag c in
    LetIn (na,b,t,c)
  | App (h,args) ->
    let h = of_constr tbl local_env tag h in
    let args = Array.map (of_constr tbl local_env tag) args in
    App (h, args)
  | Evar _ -> CErrors.anomaly Pp.(str "evar in typeops")
  | Meta _ -> CErrors.anomaly Pp.(str "meta in typeops")
  | Const (c,u) ->
    let c = hcons_con c in
    let u = UVars.Instance.hcons u in
    Const (c,u)
  | Ind (ind,u) ->
    let ind = hcons_ind ind in
    let u = UVars.Instance.hcons u in
    Ind (ind,u)
  | Construct (c,u) ->
    let c = hcons_construct c in
    let u = UVars.Instance.hcons u in
    Construct (c,u)
  | Case (ci,u,pms,(p,r),iv,c,bl) ->
    let p', bl' =
      let mib, mip = Inductive.lookup_mind_specif local_env.globals ci.ci_ind in
      let (_, (p,_), _, _, bl) = Inductive.expand_case_specif mib (destCase (gen_self tag orig)) in
      let p = Term.decompose_lambda_n_decls (mip.Declarations.mind_nrealdecls + 1) p in
      let bl = Array.map2 Term.decompose_lambda_n_decls ci.ci_cstr_ndecls bl in
      p, bl
    in
    let of_ctx (bnd, c) (bnd', _) =
      assert (Array.length bnd = List.length bnd');
      let () = hcons_inplace hcons_annot bnd in
      let local_env = push_rel_context tbl local_env bnd' in
      let c = of_constr tbl local_env tag c in
      bnd, c
    in
    let ci = hcons_caseinfo ci in
    let u = UVars.Instance.hcons u in
    let pms = Array.map (of_constr tbl local_env tag) pms in
    let p = of_ctx p p' in
    let iv = match iv with
      | NoInvert -> NoInvert
      | CaseInvert {indices} -> CaseInvert {indices=Array.map (of_constr tbl local_env tag) indices}
    in
    let c = of_constr tbl local_env tag c in
    let bl = Array.map2 of_ctx bl bl' in
    Case (ci,u,pms,(p,r),iv,c,bl)
  | Fix (ln,vrec) -> Fix (ln, of_rec_def tbl local_env tag vrec)
  | CoFix (ln,vrec) -> CoFix (ln,of_rec_def tbl local_env tag vrec)
  | Proj (p,r,c) ->
    let p = Projection.hcons p in
    let c = of_constr tbl local_env tag c in
    Proj (p,r,c)
  | Int _ as t -> t
  | Float _ as t -> t
  | String _ as t -> t
  | Array (u,t,def,ty) ->
    let u = UVars.Instance.hcons u in
    let t = Array.map (of_constr tbl local_env tag) t in
    let def = of_constr tbl local_env tag def in
    let ty = of_constr tbl local_env tag ty in
    Array (u,t,def,ty)

and of_rec_def : 't. _ -> _ -> 't gen_constr_tag -> (_ * 't array * 't array) -> _
  = fun tbl local_env tag (lna,tl,bl) ->
    let () = hcons_inplace hcons_annot lna in
    let tl = Array.map (of_constr tbl local_env tag) tl in
    let body_env = push_rec tl local_env in
    let bl = Array.map (of_constr tbl body_env tag) bl in
    (lna,tl,bl)

and push_rel_context tbl local_env ctx =
  List.fold_right (fun d local_env ->
      let d = RelDecl.map_constr_het (fun r -> r)
          (of_constr tbl local_env ConstrTag)
          d
      in
      push_decl d local_env)
    ctx
    local_env

let dbg = CDebug.create ~name:"hconstr" ()

let hcons_before_hconstr, _ = CDebug.create_full ~name:"hcons-before-hconstr" ()

let tree_size c =
  let rec aux size c =
    Constr.fold aux (size+1) c
  in
  aux 0 c

let of_constr env c =
  let c = if CDebug.get_flag hcons_before_hconstr then Constr.hcons c else c in
  let g_c = GConstr.of_constr c in
  let local_env = empty_env env in
  let local_env = iterate push_unknown_rel (Environ.nb_rel env) local_env in
  let tbl = Tbl.create 57 in
  steps := 0;
  let c = NewProfile.profile "HConstr.to_constr" (fun () ->
      of_constr tbl local_env GConstrTag g_c)
      ()
  in
  dbg Pp.(fun () ->
      let stats = Tbl.stats tbl in
      let tree_size = tree_size (self c) in
      v 0 (
        str "steps = " ++ int !steps ++ spc() ++
        str "rel cnt = " ++ int !(local_env.cnt) ++ spc() ++
        str "unknwown rels = " ++ int !(local_env.unknown_cnt) ++ spc() ++
        str "hashes = " ++ int stats.Tbl.hashes ++ spc() ++
        str "bindings = " ++ int stats.Tbl.bindings ++ spc() ++
        str "tree size = " ++ int tree_size ++ spc() ++
        str "most_collisions = " ++ int stats.Tbl.most_collisions
    )
    );
  c

let kind x = x.kind

let hcons x =
  let tbl = Tbl.create 47 in
  let module HCons = GenHCons(struct
      type nonrec t = t
      let kind = kind
      let self = self
      let refcount = refcount
        let via_hconstr = true
      module Tbl = struct
        let find_opt x = Tbl.find_opt tbl x
        let add x y = Tbl.add tbl x y
      end
    end) in
  HCons.hcons x
