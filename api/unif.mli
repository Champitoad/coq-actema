(** This module implements unification on terms. *)
(*
open Lang

(** Substitutions represent partial functions from variables 
    (represented as de Bruijn indices) to terms.  *)
module Subst : sig
  type t

  val empty : t
  val is_empty : t -> bool
  val is_bound : int -> t -> bool
  val can_bind : int -> Term.t -> t -> bool
  val bind : int -> Term.t -> t -> t
  val fetch : int -> t -> t option
  val apply : t -> Term.t -> Term.t

  (** Can also lower if int < 0. *)
  val lift : int -> t -> t

  (** This assumes that [n] --> [t] implies that [free_vars t > n]. *)
  val close : t -> t
end

(** [unify env ctx subst t1 t2] performs unification on [t1] and [t2]. 
    The terms [t1] and [t2] have free variables in [ctx]. 
    The initial substitution [subst] can be used to forbid unification 
    to substitute some variables. *)
val unify : Env.t -> Context.t -> Subst.t -> Term.t -> Term.t -> Subst.t option
*)
