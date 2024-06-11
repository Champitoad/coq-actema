(** This module implements backtraking random generators. 
    These are quickcheck-like generators that can fail and backtrack.
    
    Author : Mathis Bouverot-Dupuis. *)

open QCheck2

(** Backtracking generators form a monad. 
    Internally ['a BGen.t] is represented as ['a option Gen.t] *)
include Monad.S

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
