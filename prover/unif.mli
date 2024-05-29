(** This module handles unifying terms. 
    This is not general-purpose unification : it is tailored to the issues
    we have to solve in subformula linking. *)

open Utils.Pervasive
open Api
open Lang

(** Graphs with integer vertices. *)
module IntGraph : Graph.Sig.P

(** An item in a substitution's mapping. *)
type sitem =
  | (* This variable is rigid : it cannot be substituted.
       In other terms it is NOT a unification variable. *)
    SRigid
  | (* This variable is flexible : it can be substituted.
       In other terms it is a unification variable that has not been instantiated (yet). *)
    SFlex
  | (* This variable is a unification variable that has been instantiated.
       The term can still contain more [SFlex] or [Sbound] variables. *)
    SBound of Term.t
[@@deriving show]

(** A subtitution is the result of unifying the two sides of a link [(t1, t2)].
    For various reasons I chose to work with de Bruijn indices directly instead of 
    using explicit unification variables.

    When unifying [t1] and [t2], the free variables of [t2] are "lifted" above those of [t1],
    i.e. we add [n_free_1] to each free variable of [t2]. 
    This way we can see [t1] and [t2] as living in a "common context" 
    that has [n_free_1] + [n_free_2] variables. *)
type subst =
  { (* The number of free variables of [t1]. *)
    n_free_1 : int
  ; (* The number of free variables of [t2] (before lifting [t2]). *)
    n_free_2 : int
  ; (* The common context that [t1] and [t2] live in.
       This context has n_free_1 + n_free_2 variables. *)
    context : Context.t
  ; (* The actual substitution. It maps the free variables of the common context
       to terms that depend on these free variables.

       The domain of the mapping should be [0 ... n_free_1 + n_free_2 - 1]. *)
    mapping : sitem IntMap.t
  ; (* A graph on the variables of the common context.
       An edge [i -> j] means that variable [i] depends on variable [j], i.e.
       that [j] is in the free variables of [mapping[i]].

       We say that a substitution [subst] is acyclic when [subst.deps] is acyclic. *)
    deps : IntGraph.t
  }
[@@deriving show]

(** Test whether a substitution is closed. See [close] for more details. *)
val is_closed : subst -> bool

(** Recursively close an acyclic substitution.

    For example the open substitution 
      [x -> y + z ; y -> z ; z -> a * a]
    is equivalent to the closed substitution 
      [x -> (a * a) + (a * a) ; y -> a ; z -> a * a]

    This process does not terminate for a cyclic substitution.
*)
val close : subst -> subst

(** [apply ~repeat subst term] substitutes every free-variable in [term] that is bound by [subst]. 
    
    Using [~repeat:false] does not recursively substitute : if [subst] is cyclic,
    [apply ~repeat:false subst term] will terminate. *)
val apply : repeat:bool -> subst -> Term.t -> Term.t

(** [unify env (sitems1, ctx1, t1) (sitems2, ct2, t2)] performs syntactic unification 
    on the terms [t1] and [t2].
    The list [sitems1] gives the initial [sitem]s for the free variables of [t1] (and same for [t2]). 

    Internally the term [t2] is lifted above [t1] so that they live in the same context 
    (see [subst] for details).

    This returns a lazy sequence of all acyclic substitutions that unify [t1] and [t2].
    The returned substitutions are not necessarily closed. *)
val unify :
     Env.t
  -> sitem list * Context.t * Term.t
  -> sitem list * Context.t * Term.t
  -> subst Seq.t
