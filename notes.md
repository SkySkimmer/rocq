example:

?X := fun x => (?Y{x:=Rel 1}, ?Y{x:=Rel 1})

?Y := fun y => (?Z{x:=x; y:=Rel 1}, ?Z{x:=x; y:=Rel 1})

?Z := (x, fun _ => y)



- see ?Y{Rel 1} for the first time (in env for named with not yet computed lifts etc)
  - see ?Z{None;Rel 1} for the first time
    ?Z needs x (lift 0 + 1) y (lift 1 + 0); result = (Rel 2, fun _=> Rel 2)
    ie 0 (resp 1) more lifts from Z for x (resp y)
    put ?Z{x := [Rel 2]; y := [Rel 2]} -> result in cache
    (use min final lift for each, no need for all or intermediate)
    here it's 0 so trivial but not in general
  - see ?Z{None;Rel 1} for the second time
    evaluate needed args at needed lifts
    lookup in cache -> found
  ?Y needs x (lift 1)
  etc

problem: this only shares when args are the same
we would like to share subterms which don't use the args too, is that possible?

maybe we can remember which paths use which args?

eg in ?A{x;y} := cons x (cons y (cons 0 nil))
the first 2 cons and the (cons 0 nil) don't depend on args

type skeleton =
  | NoArgsUsed of constr
  | ArgsUsed of { args_used : Id.Set.t; kind : skeleton kind }

then we have val instantiate_skeleton : substituend Id.Map.t -> skeleton -> constr
(maybe with some int lifts next to substituend)

but what do we do on ?A{x;y=1}? should produce (cons x (cons 1 (cons 0 nil)))

DefnEvar of { evar : Evar.t; args : skeleton SList.t (* skip non needed ones *);
              evar_body : skeleton;
              mutable self : skeleton option; }

if self = Some, it's the instantiation_skeleton of the evar_body with the args ??
but that won't share properly
keep a previously computed at different args constr around? then use it when NoVars?



the cache contains both the fully computed values and the skeletons?
(don't care too much about when only a subset of args are different for now
future work: give a uid to each encountered arg, then we can cache instantiations in the skeleton?)

there is also sharing from args, eg
?A{x} := (x, x)
but that is already handled AFAICT

theorem:
forall c c' n, lift n c = lift n c' -> forall m, lift m c = lift m c'
