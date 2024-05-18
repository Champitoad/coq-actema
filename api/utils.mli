open Batteries
module IntSet : Set.S with type elt = int
module IntMap : Map.S with type key = int
module StringMap : Map.S with type key = string

(** This module implements Backtraking random generators. 
    These are quickcheck-like generators that can fail and backtrack. *)
module BGen : sig
  open QCheck2

  (** Backtracking generators ['a BGen.t] are represented as ['a option Gen.t]. *)
  type 'a t

  (** Monad return. *)
  val return : 'a -> 'a t

  (** Functor map. *)
  val map : ('a -> 'b) -> 'a t -> 'b t

  (** Monad bind. *)
  val bind : 'a t -> ('a -> 'b t) -> 'b t

  (** Failing is the first component of backtracking. *)
  val fail : unit -> 'a t

  (** Fail if the condition is false. *)
  val guard : ('a -> bool) -> 'a t -> 'a t

  (** Fail if the condition is false. 
      The generator is not asked to produce any output if the condition is false. *)
  val cond : bool -> 'a t -> 'a t

  (** Lift a [Gen.t] generator to a [BGen.t] which always succeeds. *)
  val lift : 'a Gen.t -> 'a t

  (** Run a backtracking generator until it succeeds. Caution : this may not terminate ! *)
  val run : 'a t -> 'a Gen.t

  (** Run a backtracking generator. *)
  val run_opt : 'a t -> 'a option Gen.t

  (** [first gens] is a backtracking point : it will run the generators in [gens] in order,
      returning the first one that succeeds (and fails if they all fail). *)
  val first : 'a t list -> 'a t

  (** [oneof gens] is a backtracking point : it will choose a generator in [gens]
      and if it fails it will discard it, choose another one and repeat.
      This fails if and only if all generators in [gens] fail. *)
  val oneof : 'a t list -> 'a t

  (** [oneofl xs] will randomly choose an element of [xs], or fail if [xs] is empty. *)
  val oneofl : 'a list -> 'a t

  (** [frequency weighted_gens] is a backtracking point. *)
  val frequency : (int * 'a t) list -> 'a t

  (** For convenience we provide alternative syntax for some operators. *)
  module Syntax : sig
    (** Let-style functor map. *)
    val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t

    (** Infix functor map. *)
    val ( <$> ) : ('a -> 'b) -> 'a t -> 'b t

    (** Applicative syntax. *)
    val ( <*> ) : ('a -> 'b) t -> 'a t -> 'b t

    (** Let-style monad bind. *)
    val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t

    (** Infix monad bind. *)
    val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t

    (** Infix monad bind, with arguments reversed. *)
    val ( =<< ) : ('a -> 'b t) -> 'a t -> 'b t
  end
end

(** This module implements bijections between finite sets, i.e. bi-directional maps. *)
module BiMap : sig
  type ('a, 'b) t

  val bindings : ('a, 'b) t -> ('a * 'b) list
  val empty : ('a, 'b) t
  val inverse : ('a, 'b) t -> ('b, 'a) t
  val add : 'a -> 'b -> ('a, 'b) t -> ('a, 'b) t
  val remove : 'a -> ('a, 'b) t -> ('a, 'b) t
  val union : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
  val find : 'a -> ('a, 'b) t -> 'b
  val find_opt : 'a -> ('a, 'b) t -> 'b option
  val domain : ('a, 'b) t -> 'a list
  val codomain : ('a, 'b) t -> 'b list
  val kdiff : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
  val vdiff : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
  val of_seq : ('a * 'b) Seq.t -> ('a, 'b) t
end
