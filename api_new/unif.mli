(** This module implements unification on terms. *)

open Lang

type sitem = Sbound of Term.t | Sflex
type 'a eqns = ('a * 'a) list

(** Substitutions. *)
module Subst : sig
  type t

  exception UnboundVariable of Name.t * t

  val empty : t
  val is_empty : t -> bool
  val aslist : t -> (Name.t * sitem) list
  val oflist : (Name.t * sitem) list -> t
  val fold : ('a -> Name.t * sitem -> 'a) -> 'a -> Name.t -> 'a
  val add : Name.t -> Term.t -> t -> t
  val push : Name.t -> sitem -> t -> t
  val fetch : Name.t -> t -> Term.t
  val get_tag : Name.t -> t -> sitem option
  val is_complete : t -> bool
  val f_apply1 : Name.t -> Term.t -> Term.t -> Term.t
  val f_iter : t -> int -> Term.t -> Term.t
  val f_apply : t -> Term.t -> Term.t
  val close : t -> t
  val to_string : t -> string
end

val unify : Env.t -> Context.t -> Subst.t -> Term.t eqns -> Subst.t option
