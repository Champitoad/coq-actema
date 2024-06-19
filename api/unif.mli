(** This module handles unification of terms. 
    This is not general-purpose unification : it is tailored to the issues
    we have to solve in subformula linking, such as dealing with dependencies between 
    unification variables.
    
    For the moment we implement syntactic unification only (no beta or eta reduction, 
    no unfolding of constants). *)

open Lang

(** A substitution is a mapping from free variables to terms 
    (which may themselves contain free variables). *)
type subst [@@deriving show]

(** [is_rigid subst fvar] checks whether [fvar] is rigid in [subst], 
    i.e. it can't be bound to anything. *)
val is_rigid : subst -> FVarId.t -> bool

(** [is_bound subst fvar] checks whether [fvar] is bound to a term in [subst]. *)
val is_bound : subst -> FVarId.t -> bool

(** [is_flex subst fvar] checks whether [fvar] is flex in [subst],
    i.e. it is not bound to any term but it is not rigid. *)
val is_flex : subst -> FVarId.t -> bool

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
