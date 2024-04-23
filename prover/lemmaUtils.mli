(** This module defines functions to manipulate the lemma database. *)

open CoreLogic

(** This module defines predicates on lemmas. *)
module Pred : sig
  (** A predicate on lemmas. The first argument is the lemma full name, 
      the second argument is the lemma user name and statement. *)
  type t = Proof.proof -> Proof.lemma -> bool

  (** [true_] is the predicate that always returns [true], regardless of its arguments. *)
  val true_ : t

  (** [false_] is the predicate that always returns [false], regardless of its arguments. *)
  val false_ : t

  (** [and_ p1 p2] returns [true] if and only if both [p1] and [p2] return [true]. *)
  val and_ : t -> t -> t

  (** [or_ p1 p2] returns [true] if and only if at least one of [p1] and [p2] returns [true]. *)
  val or_ : t -> t -> t

  (** [all ps] returns [true] if and only if all predicates in [ps] return [true]. *)
  val all : t list -> t

  (** [all ps] returns [true] if and only if at least one predicate in [ps] returns [true]. *)
  val any : t list -> t

  (** Find lemmas whose name matches a given pattern. *)
  val match_name : string -> t

  (** Find lemmas that have a subformula linking interaction with a given selection. *)
  val link_sfl : IPath.t -> t

  (** Find lemmas that have a deep rewrite interaction with a given selection. *)
  val link_drewrite : IPath.t -> t
end

(** Filter the lemma database by keeping only the lemmas that satisfy the given predicate. 
    This only changes the lemma database.  *)
val filter : Pred.t -> Proof.proof -> Proof.proof
