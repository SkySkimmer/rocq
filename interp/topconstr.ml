(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(*i*)
open Pp
open Util
open Names
open Nameops
open Libnames
open Rawterm
open Term
(*i*)

(**********************************************************************)
(* This is the subtype of rawconstr allowed in syntactic extensions *)

type aconstr =
  (* Part common to rawconstr and cases_pattern *)
  | ARef of global_reference
  | AVar of identifier
  | AApp of aconstr * aconstr list
  (* Part only in rawconstr *)
  | ALambda of name * aconstr * aconstr
  | AProd of name * aconstr * aconstr
  | ALetIn of name * aconstr * aconstr
  | ACases of aconstr option * aconstr option *
      (aconstr * (name * (inductive * name list) option)) list *
      (identifier list * cases_pattern list * aconstr) list
  | AOrderedCase of case_style * aconstr option * aconstr * aconstr array
  | ALetTuple of name list * (name * aconstr option) * aconstr * aconstr
  | AIf of aconstr * (name * aconstr option) * aconstr * aconstr
  | ASort of rawsort
  | AHole of hole_kind
  | APatVar of patvar
  | ACast of aconstr * aconstr
  
let name_app f e = function
  | Name id -> let (id, e) = f id e in (Name id, e)
  | Anonymous -> Anonymous, e

let rawconstr_of_aconstr_with_binders loc g f e = function
  | AVar id -> RVar (loc,id)
  | AApp (a,args) -> RApp (loc,f e a, List.map (f e) args)
  | ALambda (na,ty,c) ->
      let na,e = name_app g e na in RLambda (loc,na,f e ty,f e c)
  | AProd (na,ty,c) ->
      let na,e = name_app g e na in RProd (loc,na,f e ty,f e c)
  | ALetIn (na,b,c) ->
      let na,e = name_app g e na in RLetIn (loc,na,f e b,f e c)
  | ACases (tyopt,rtntypopt,tml,eqnl) ->
      let cases_predicate_names tml =
	List.flatten (List.map (function
	  | (tm,(na,None)) -> [na]
	  | (tm,(na,Some (_,nal))) -> na::nal) tml) in
      (* TODO: apply g to na (in fact not used) *)
      let e' = List.fold_right
	(fun na e -> snd (name_app g e na)) (cases_predicate_names tml) e in
      let fold id (idl,e) = let (id,e) = g id e in (id::idl,e) in
      let eqnl = List.map (fun (idl,pat,rhs) ->
        let (idl,e) = List.fold_right fold idl ([],e) in (loc,idl,pat,f e rhs)) eqnl in
      RCases (loc,(option_app (f e) tyopt, ref (option_app (f e') rtntypopt)),
        List.map (fun (tm,(na,x)) -> 
	  (f e tm,ref (na,option_app (fun (x,y) -> (loc,x,y)) x))) tml,eqnl)
  | AOrderedCase (b,tyopt,tm,bv) ->
      ROrderedCase (loc,b,option_app (f e) tyopt,f e tm,Array.map (f e) bv,ref None)
  | ALetTuple (nal,(na,po),b,c) ->
      RLetTuple (loc,nal,(na,option_app (f e) po),f e b,f e c)
  | AIf (c,(na,po),b1,b2) ->
      RIf (loc,f e c,(na,option_app (f e) po),f e b1,f e b2)
  | ACast (c,t) -> RCast (loc,f e c,f e t)
  | ASort x -> RSort (loc,x)
  | AHole x  -> RHole (loc,x)
  | APatVar n -> RPatVar (loc,(false,n))
  | ARef x -> RRef (loc,x)

let rec subst_pat subst pat = 
  match pat with
  | PatVar _ -> pat
  | PatCstr (loc,((kn,i),j),cpl,n) -> 
      let kn' = subst_kn subst kn 
      and cpl' = list_smartmap (subst_pat subst) cpl in
        if kn' == kn && cpl' == cpl then pat else
          PatCstr (loc,((kn',i),j),cpl',n)

let rec subst_aconstr subst raw =
  match raw with
  | ARef ref -> 
      let ref' = subst_global subst ref in 
	if ref' == ref then raw else
	  ARef ref'

  | AVar _ -> raw

  | AApp (r,rl) -> 
      let r' = subst_aconstr subst r 
      and rl' = list_smartmap (subst_aconstr subst) rl in
	if r' == r && rl' == rl then raw else
	  AApp(r',rl')

  | ALambda (n,r1,r2) -> 
      let r1' = subst_aconstr subst r1 and r2' = subst_aconstr subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  ALambda (n,r1',r2')

  | AProd (n,r1,r2) -> 
      let r1' = subst_aconstr subst r1 and r2' = subst_aconstr subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  AProd (n,r1',r2')

  | ALetIn (n,r1,r2) -> 
      let r1' = subst_aconstr subst r1 and r2' = subst_aconstr subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  ALetIn (n,r1',r2')

  | ACases (ro,rtntypopt,rl,branches) -> 
      let ro' = option_smartmap (subst_aconstr subst) ro 
      and rtntypopt' = option_smartmap (subst_aconstr subst) rtntypopt
      and rl' = list_smartmap
        (fun (a,(n,signopt) as x) -> 
	  let a' = subst_aconstr subst a in
	  let signopt' = option_app (fun ((indkn,i),nal as z) ->
	    let indkn' = subst_kn subst indkn in
	    if indkn == indkn' then z else ((indkn',i),nal)) signopt in
	  if a' == a && signopt' == signopt then x else (a',(n,signopt')))
        rl
      and branches' = list_smartmap 
                        (fun (idl,cpl,r as branch) ->
                           let cpl' = list_smartmap (subst_pat subst) cpl
                           and r' = subst_aconstr subst r in
                             if cpl' == cpl && r' == r then branch else
                               (idl,cpl',r'))
                        branches
      in
        if ro' == ro && rtntypopt == rtntypopt' &
          rl' == rl && branches' == branches then raw else
          ACases (ro',rtntypopt',rl',branches')

  | AOrderedCase (b,ro,r,ra) -> 
      let ro' = option_smartmap (subst_aconstr subst) ro
      and r' = subst_aconstr subst r 
      and ra' = array_smartmap (subst_aconstr subst) ra in
	if ro' == ro && r' == r && ra' == ra then raw else
	  AOrderedCase (b,ro',r',ra')

  | ALetTuple (nal,(na,po),b,c) ->
      let po' = option_smartmap (subst_aconstr subst) po
      and b' = subst_aconstr subst b 
      and c' = subst_aconstr subst c in
	if po' == po && b' == b && c' == c then raw else
	  ALetTuple (nal,(na,po'),b',c')

  | AIf (c,(na,po),b1,b2) ->
      let po' = option_smartmap (subst_aconstr subst) po
      and b1' = subst_aconstr subst b1
      and b2' = subst_aconstr subst b2 
      and c' = subst_aconstr subst c in
	if po' == po && b1' == b1 && b2' == b2 && c' == c then raw else
	  AIf (c',(na,po'),b1',b2')

  | APatVar _ | ASort _ -> raw

  | AHole (ImplicitArg (ref,i)) ->
      let ref' = subst_global subst ref in 
	if ref' == ref then raw else
	  AHole (ImplicitArg (ref',i))
  | AHole (BinderType _ | QuestionMark | CasesType |
      InternalHole | TomatchTypeParameter _) -> raw

  | ACast (r1,r2) -> 
      let r1' = subst_aconstr subst r1 and r2' = subst_aconstr subst r2 in
	if r1' == r1 && r2' == r2 then raw else
	  ACast (r1',r2')

let add_name r = function
  | Anonymous -> ()
  | Name id -> r := id :: !r

let aconstr_of_rawconstr vars a =
  let found = ref [] in
  let bound_binders = ref [] in
  let rec aux = function
  | RVar (_,id) -> 
      if not (List.mem id !bound_binders) then found := id::!found;
      AVar id
  | RApp (_,g,args) -> AApp (aux g, List.map aux args)
  | RLambda (_,na,ty,c) -> add_name bound_binders na; ALambda (na,aux ty,aux c)
  | RProd (_,na,ty,c) -> add_name bound_binders na; AProd (na,aux ty,aux c)
  | RLetIn (_,na,b,c) -> add_name bound_binders na; ALetIn (na,aux b,aux c)
  | RCases (_,(tyopt,rtntypopt),tml,eqnl) ->
      let f (_,idl,pat,rhs) =
        bound_binders := idl@(!bound_binders);
        (idl,pat,aux rhs) in
      ACases (option_app aux tyopt,
        option_app aux !rtntypopt,
        List.map (fun (tm,{contents = (na,x)}) ->
	  add_name bound_binders na;
	  option_iter
	    (fun (_,_,nl) -> List.iter (add_name bound_binders) nl) x;
          (aux tm,(na,option_app (fun (_,ind,nal) -> (ind,nal)) x))) tml,
        List.map f eqnl)
  | ROrderedCase (_,b,tyopt,tm,bv,_) ->
      AOrderedCase (b,option_app aux tyopt,aux tm, Array.map aux bv)
  | RLetTuple (loc,nal,(na,po),b,c) ->
      ALetTuple (nal,(na,option_app aux po),aux b,aux c)
  | RIf (loc,c,(na,po),b1,b2) ->
      AIf (aux c,(na,option_app aux po),aux b1,aux b2)
  | RCast (_,c,t) -> ACast (aux c,aux t)
  | RSort (_,s) -> ASort s
  | RHole (_,w) -> AHole w
  | RRef (_,r) -> ARef r
  | RPatVar (_,(_,n)) -> APatVar n
  | RDynamic _ | RRec _ | REvar _ ->
      error "Fixpoints, cofixpoints, existential variables and pattern-matching  not \
allowed in abbreviatable expressions"
  in
  let a = aux a in
  let check_type x =
    if not (List.mem x !found or List.mem x !bound_binders) then
      error ((string_of_id x)^" is unbound in the right-hand-side") in
  List.iter check_type vars;
  a

(* Pattern-matching rawconstr and aconstr *)

let rec adjust_scopes = function
  | _,[] -> []
  | [],a::args -> (None,a) :: adjust_scopes ([],args)
  | sc::scopes,a::args -> (sc,a) :: adjust_scopes (scopes,args)

exception No_match

let rec alpha_var id1 id2 = function
  | (i1,i2)::_ when i1=id1 -> i2 = id2
  | (i1,i2)::_ when i2=id2 -> i1 = id1
  | _::idl -> alpha_var id1 id2 idl
  | [] -> id1 = id2

let alpha_eq_val (x,y) = x = y

let bind_env sigma var v =
  try
    let vvar = List.assoc var sigma in
    if alpha_eq_val (v,vvar) then sigma
    else raise No_match
  with Not_found ->
    (* TODO: handle the case of multiple occs in different scopes *)
    (var,v)::sigma

let rec match_ alp metas sigma a1 a2 = match (a1,a2) with
  | r1, AVar id2 when List.mem id2 metas -> bind_env sigma id2 r1
  | RVar (_,id1), AVar id2 when alpha_var id1 id2 alp -> sigma
  | RRef (_,r1), ARef r2 when r1 = r2 -> sigma
  | RPatVar (_,(_,n1)), APatVar n2 when n1=n2 -> sigma
  | RApp (_,f1,l1), AApp (f2,l2) when List.length l1 = List.length l2 ->
      List.fold_left2 (match_ alp metas) (match_ alp metas sigma f1 f2) l1 l2
  | RLambda (_,na1,t1,b1), ALambda (na2,t2,b2) ->
     match_binders alp metas (match_ alp metas sigma t1 t2) b1 b2 na1 na2
  | RProd (_,na1,t1,b1), AProd (na2,t2,b2) ->
     match_binders alp metas (match_ alp metas sigma t1 t2) b1 b2 na1 na2
  | RLetIn (_,na1,t1,b1), AProd (na2,t2,b2) ->
     match_binders alp metas (match_ alp metas sigma t1 t2) b1 b2 na1 na2
  | RCases (_,(po1,rtno1),tml1,eqnl1), ACases (po2,rtno2,tml2,eqnl2) 
      when List.length tml1 = List.length tml2 ->
     let sigma = option_fold_left2 (match_ alp metas) sigma po1 po2 in
     (* TODO: match rtno' with their contexts *)
     let sigma = List.fold_left2 
       (fun s (tm1,_) (tm2,_) -> match_ alp metas s tm1 tm2) sigma tml1 tml2 in
     List.fold_left2 (match_equations alp metas) sigma eqnl1 eqnl2
  | ROrderedCase (_,st,po1,c1,bl1,_), AOrderedCase (st2,po2,c2,bl2) ->
     let sigma = option_fold_left2 (match_ alp metas) sigma po1 po2 in
     array_fold_left2 (match_ alp metas) (match_ alp metas sigma c1 c2) bl1 bl2
  | RCast(_,c1,t1), ACast(c2,t2) ->
      match_ alp metas (match_ alp metas sigma c1 c2) t1 t2
  | RSort (_,s1), ASort s2 when s1 = s2 -> sigma
  | RPatVar _, AHole _ -> (*Don't hide Metas, they bind in ltac*) raise No_match
  | a, AHole _ when not(Options.do_translate()) -> sigma
  | RHole _, AHole _ -> sigma
  | (RDynamic _ | RRec _ | REvar _), _ 
  | _,_ -> raise No_match

and match_binders alp metas sigma b1 b2 na1 na2 = match (na1,na2) with
  | (na1,Name id2) when List.mem id2 metas ->
      let sigma =
	name_fold
	  (fun id sigma -> bind_env sigma id2 (RVar (dummy_loc,id))) na1 sigma
      in 
      match_ alp metas sigma b1 b2
  | (na1,na2) -> 
      let alp =
        name_fold
	  (fun id1 -> name_fold (fun id2 alp -> (id1,id2)::alp) na2) na1 alp in
      match_ alp metas sigma b1 b2

and match_equations alp metas sigma (_,idl1,pat1,rhs1) (idl2,pat2,rhs2) =
  if idl1 = idl2 & pat1 = pat2 (* Useful to reason up to alpha ?? *) then
    match_ alp metas sigma rhs1 rhs2
  else raise No_match

type scope_name = string

type interpretation = 
    (identifier * (scope_name option * scope_name list)) list * aconstr

let match_aconstr c (metas_scl,pat) =
  let subst = match_ [] (List.map fst metas_scl) [] c pat in
  (* Reorder canonically the substitution *)
  let find x subst =
    try List.assoc x subst
    with Not_found ->
      (* Happens for binders bound to Anonymous *)
      (* Find a better way to propagate Anonymous... *)
      RVar (dummy_loc,x) in
  List.map (fun (x,scl) -> (find x subst,scl)) metas_scl

(**********************************************************************)
(*s Concrete syntax for terms *)

type notation = string

type explicitation = ExplByPos of int | ExplByName of identifier

type proj_flag = int option (* [Some n] = proj of the n-th visible argument *)

type cases_pattern_expr =
  | CPatAlias of loc * cases_pattern_expr * identifier
  | CPatCstr of loc * reference * cases_pattern_expr list
  | CPatAtom of loc * reference option
  | CPatNotation of loc * notation * cases_pattern_expr list
  | CPatNumeral of loc * Bignat.bigint
  | CPatDelimiters of loc * string * cases_pattern_expr

type constr_expr =
  | CRef of reference
  | CFix of loc * identifier located * fixpoint_expr list
  | CCoFix of loc * identifier located * cofixpoint_expr list
  | CArrow of loc * constr_expr * constr_expr
  | CProdN of loc * (name located list * constr_expr) list * constr_expr
  | CLambdaN of loc * (name located list * constr_expr) list * constr_expr
  | CLetIn of loc * name located * constr_expr * constr_expr
  | CAppExpl of loc * (proj_flag * reference) * constr_expr list
  | CApp of loc * (proj_flag * constr_expr) * 
      (constr_expr * explicitation located option) list
  | CCases of loc * (constr_expr option * constr_expr option) *
      (constr_expr * (name * constr_expr option)) list *
      (loc * cases_pattern_expr list * constr_expr) list
  | COrderedCase of loc * case_style * constr_expr option * constr_expr
      * constr_expr list
  | CLetTuple of loc * name list * (name * constr_expr option) *
      constr_expr * constr_expr
  | CIf of loc * constr_expr * (name * constr_expr option)
      * constr_expr * constr_expr
  | CHole of loc
  | CPatVar of loc * (bool * patvar)
  | CEvar of loc * existential_key
  | CSort of loc * rawsort
  | CCast of loc * constr_expr * constr_expr
  | CNotation of loc * notation * constr_expr list
  | CNumeral of loc * Bignat.bigint
  | CDelimiters of loc * string * constr_expr
  | CDynamic of loc * Dyn.t

and fixpoint_expr = identifier * int * constr_expr * constr_expr

and cofixpoint_expr = identifier * constr_expr * constr_expr

(***********************)
(* For binders parsing *)

type local_binder =
  | LocalRawDef of name located * constr_expr
  | LocalRawAssum of name located list * constr_expr

let rec local_binders_length = function
  | [] -> 0
  | LocalRawDef _::bl -> 1 + local_binders_length bl
  | LocalRawAssum (idl,_)::bl -> List.length idl + local_binders_length bl

(**********************************************************************)
(* Functions on constr_expr *)

let constr_loc = function
  | CRef (Ident (loc,_)) -> loc
  | CRef (Qualid (loc,_)) -> loc
  | CFix (loc,_,_) -> loc
  | CCoFix (loc,_,_) -> loc
  | CArrow (loc,_,_) -> loc
  | CProdN (loc,_,_) -> loc
  | CLambdaN (loc,_,_) -> loc
  | CLetIn (loc,_,_,_) -> loc
  | CAppExpl (loc,_,_) -> loc
  | CApp (loc,_,_) -> loc
  | CCases (loc,_,_,_) -> loc
  | COrderedCase (loc,_,_,_,_) -> loc
  | CLetTuple (loc,_,_,_,_) -> loc
  | CIf (loc,_,_,_,_) -> loc
  | CHole loc -> loc
  | CPatVar (loc,_) -> loc
  | CEvar (loc,_) -> loc
  | CSort (loc,_) -> loc
  | CCast (loc,_,_) -> loc
  | CNotation (loc,_,_) -> loc
  | CNumeral (loc,_) -> loc
  | CDelimiters (loc,_,_) -> loc
  | CDynamic _ -> dummy_loc

let cases_pattern_loc = function
  | CPatAlias (loc,_,_) -> loc
  | CPatCstr (loc,_,_) -> loc
  | CPatAtom (loc,_) -> loc
  | CPatNotation (loc,_,_) -> loc
  | CPatNumeral (loc,_) -> loc
  | CPatDelimiters (loc,_,_) -> loc

let occur_var_constr_ref id = function
  | Ident (loc,id') -> id = id'
  | Qualid _ -> false

let rec occur_var_constr_expr id = function
  | CRef r -> occur_var_constr_ref id r
  | CArrow (loc,a,b) -> occur_var_constr_expr id a or occur_var_constr_expr id b
  | CAppExpl (loc,(_,r),l) ->
      occur_var_constr_ref id r or List.exists (occur_var_constr_expr id) l
  | CApp (loc,(_,f),l) ->
      occur_var_constr_expr id f or
      List.exists (fun (a,_) -> occur_var_constr_expr id a) l
  | CProdN (_,l,b) -> occur_var_binders id b l
  | CLambdaN (_,l,b) -> occur_var_binders id b l
  | CLetIn (_,na,a,b) -> occur_var_binders id b [[na],a]
  | CCast (loc,a,b) -> occur_var_constr_expr id a or occur_var_constr_expr id b
  | CNotation (_,_,l) -> List.exists (occur_var_constr_expr id) l
  | CDelimiters (loc,_,a) -> occur_var_constr_expr id a
  | CHole _ | CEvar _ | CPatVar _ | CSort _ | CNumeral _ | CDynamic _ -> false
  | CCases (loc,_,_,_) 
  | COrderedCase (loc,_,_,_,_) 
  | CLetTuple (loc,_,_,_,_) 
  | CIf (loc,_,_,_,_) 
  | CFix (loc,_,_) 
  | CCoFix (loc,_,_) -> 
      Pp.warning "Capture check in multiple binders not done"; false

and occur_var_binders id b = function
  | (idl,a)::l -> 
      occur_var_constr_expr id a or
      (not (List.mem (Name id) (snd (List.split idl)))
      & occur_var_binders id b l)
  | [] -> occur_var_constr_expr id b

let mkIdentC id  = CRef (Ident (dummy_loc, id))
let mkRefC r     = CRef r
let mkAppC (f,l) = CApp (dummy_loc, (None,f), List.map (fun x -> (x,None)) l)
let mkCastC (a,b)  = CCast (dummy_loc,a,b)
let mkLambdaC (idl,a,b) = CLambdaN (dummy_loc,[idl,a],b)
let mkLetInC (id,a,b)   = CLetIn (dummy_loc,id,a,b)
let mkProdC (idl,a,b)   = CProdN (dummy_loc,[idl,a],b)

(* Used in correctness and interface *)


let names_of_cases_indtype =
  let rec vars_of ids t =
    match t with
      (* We deal only with the regular cases *)
      | CApp (_,_,l) -> List.fold_left (fun ids (a,_) -> vars_of ids a) [] l
      | CRef (Ident (_,id)) -> id::ids
      | CNotation (_,_,l)
      (* assume the ntn is applicative and does not instantiate the head !! *)
      | CAppExpl (_,_,l) -> List.fold_left vars_of [] l
      | CDelimiters(_,_,c) -> vars_of ids c
      | _ -> ids in
  vars_of []

let map_binder g e nal = List.fold_right (fun (_,na) -> name_fold g na) nal e

let map_binders f g e bl =
  (* TODO: avoid variable capture in [t] by some [na] in [List.tl nal] *)
  let h (nal,t) (e,bl) = (map_binder g e nal,(nal,f e t)::bl) in
  List.fold_right h bl (e,[])

let map_constr_expr_with_binders f g e = function
  | CArrow (loc,a,b) -> CArrow (loc,f e a,f e b)
  | CAppExpl (loc,r,l) -> CAppExpl (loc,r,List.map (f e) l) 
  | CApp (loc,(p,a),l) -> 
      CApp (loc,(p,f e a),List.map (fun (a,i) -> (f e a,i)) l)
  | CProdN (loc,bl,b) ->
      let (e,bl) = map_binders f g e bl in CProdN (loc,bl,f e b)
  | CLambdaN (loc,bl,b) ->
      let (e,bl) = map_binders f g e bl in CLambdaN (loc,bl,f e b)
  | CLetIn (loc,na,a,b) -> CLetIn (loc,na,f e a,f (name_fold g (snd na) e) b)
  | CCast (loc,a,b) -> CCast (loc,f e a,f e b)
  | CNotation (loc,n,l) -> CNotation (loc,n,List.map (f e) l)
  | CDelimiters (loc,s,a) -> CDelimiters (loc,s,f e a)
  | CHole _ | CEvar _ | CPatVar _ | CSort _ 
  | CNumeral _ | CDynamic _ | CRef _ as x -> x
  | CCases (loc,(po,rtnpo),a,bl) ->
      (* TODO: apply g on the binding variables in pat... *)
      let bl = List.map (fun (loc,pat,rhs) -> (loc,pat,f e rhs)) bl in
      let e' = 
	List.fold_right
	  (fun (tm,(na,indnal)) e ->
	    option_fold_right
	      (fun t ->
		let ids = names_of_cases_indtype t in
		List.fold_right g ids) indnal (name_fold g na e))
	  a e
      in
      CCases (loc,(option_app (f e) po, option_app (f e') rtnpo),
         List.map (fun (tm,x) -> (f e tm,x)) a,bl)
  | COrderedCase (loc,s,po,a,bl) ->
      COrderedCase (loc,s,option_app (f e) po,f e a,List.map (f e) bl)
  | CLetTuple (loc,nal,(na,po),b,c) ->
      let e' = List.fold_right (name_fold g) nal e in
      let e'' = name_fold g na e in
      CLetTuple (loc,nal,(na,option_app (f e'') po),f e b,f e' c)
  | CIf (loc,c,(na,po),b1,b2) ->
      let e' = name_fold g na e in
      CIf (loc,f e c,(na,option_app (f e') po),f e b1,f e b2)
  | CFix (loc,id,dl) ->
      CFix (loc,id,List.map (fun (id,n,t,d) -> (id,n,f e t,f e d)) dl)
  | CCoFix (loc,id,dl) ->
      CCoFix (loc,id,List.map (fun (id,t,d) -> (id,f e t,f e d)) dl)

(* Used in constrintern *)
let rec replace_vars_constr_expr l = function
  | CRef (Ident (loc,id)) as x ->
      (try CRef (Ident (loc,List.assoc id l)) with Not_found -> x)
  | c -> map_constr_expr_with_binders replace_vars_constr_expr 
      (fun id l -> List.remove_assoc id l) l c

(**********************************************************************)
(* Concrete syntax for modules and modules types *)

type with_declaration_ast = 
  | CWith_Module of identifier * qualid located
  | CWith_Definition of identifier * constr_expr

type module_type_ast = 
  | CMTEident of qualid located
  | CMTEwith of module_type_ast * with_declaration_ast

type module_ast = 
  | CMEident of qualid located
  | CMEapply of module_ast * module_ast
