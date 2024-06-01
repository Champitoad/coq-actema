(** This module handles unifying terms. 
    This is not general-purpose unification : it is tailored to the issues
    we have to solve in subformula linking. *)

open Api
open Lang

(** A substitution is a mapping from free variables to terms 
    (which may themselves contain free variables). *)
type subst [@@deriving show]

(** [apply subst term] substitutes every free variable of [term] that is bound by [subst]. *)
val apply : subst -> Term.t -> Term.t

(** [unify env ctx ?rigid_fvars ?forbidden_deps t1 t2] performs syntactic unification on the terms [t1] and [t2].
    - [env] is the global environment [t1] and [t2] live in. 
    - [ctx] is a local context that contains the free variables of both [t1] and [t2].
    - [rigid_fvars] specifies a list of free variables that are rigid, i.e. can't be substituted
      for something else. By default this list is empty.
    - [forbidden_deps] specifies a list of pairs of free variables [(f1, f2)] that indicate
      that [f1] is not allowed to depend on [f2]. By default this list is empty.
    
    If this succeeds this will return a substitution [Some subst] such that : 
    - [apply subst t1] and [apply subst t2] are alpha equivalent.
    - The dependency graph associated to [subst] is acyclic. 
    - [subst] is closed.
    
    It will return [None] only if no such substitution exists. *)
val unify :
     Env.t
  -> Context.t
  -> ?rigid_fvars:FVarId.t list
  -> ?forbidden_deps:(FVarId.t * FVarId.t) list
  -> Term.t
  -> Term.t
  -> subst option

(*= { context : Context.t; map : sitem FVarId.Map.t ; deps : FVarGraph.t}*)

(** Test whether the dependency graph of the substitution contains a cycle. *)
(*val is_cyclic : subst -> bool

  (** Recursively close an acyclic substitution.

      For example the open substitution
        [x -> y + z ; y -> z ; z -> a * a]
      is equivalent to the closed substitution
        [x -> (a * a) + (a * a) ; y -> a ; z -> a * a]

      This process does not terminate for a cyclic substitution.
  *)
  val close : subst -> subst

  (** Test whether a substitution is closed. See [close] for more details. *)
  val is_closed : subst -> bool*)
