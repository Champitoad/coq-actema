(** This module implements some basic but very useful monads. 
    
    There is nothing fancy going on here, in particular no monad transformers
    (although they could be added in the future). *)

(**************************************************************************************)

(** All the operations a monad gives us access to. *)
module type S = sig
  type 'a t

  (** Monadic return. *)
  val return : 'a -> 'a t

  (** Functorial map. *)
  val map : ('a -> 'b) -> 'a t -> 'b t

  (** Monadic bind. *)
  val bind : 'a t -> ('a -> 'b t) -> 'b t

  (** Monadic join. *)
  val join : 'a t t -> 'a t

  (** Infix map. *)
  val ( <$> ) : ('a -> 'b) -> 'a t -> 'b t

  (** Applicative stuff. *)
  val ( <*> ) : ('a -> 'b) t -> 'a t -> 'b t

  (** Infix bind. *)
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t

  (** Reversed infix bind. *)
  val ( =<< ) : ('a -> 'b t) -> 'a t -> 'b t

  (** Let-style map. *)
  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t

  (** Let-style bind. *)
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t

  (** Sequence a list of monadic actions, one after the other. *)
  val sequence : 'a t list -> 'a list t

  (** Map a monadic action over a list. *)
  val mapM : ('a -> 'b t) -> 'a list -> 'b list t

  (** Fold a monadic action over a list. *)
  val foldM : ('acc -> 'a -> 'acc t) -> 'acc -> 'a list -> 'acc t
end

(**************************************************************************************)

(** Make a monad from a minimal set of operations. *)
module Make (M : sig
  type 'a t

  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end) : S with type 'a t = 'a M.t

(**************************************************************************************)
(** Some useful monads. *)

(** The standard option monad. *)
module Option : S with type 'a t = 'a option

(** The standard list monad. *)
module List : S with type 'a t = 'a list

(** The standard reader monad over some type [T.t].
    This provides read-only access to a value of type [T.t]. *)
module Reader (T : sig
  type t
end) : sig
  include S with type 'a t = T.t -> 'a

  (** Get the current environment. *)
  val get : T.t t

  (** Run the reader monad in some environment. *)
  val run : T.t -> 'a t -> 'a
end

(** The standard state monad over some type [T.t].
    This provides read-write access to a value of type [T.t]. *)
module State (T : sig
  type t
end) : sig
  include S with type 'a t = T.t -> 'a * T.t

  (** Get the current state. *)
  val get : T.t t

  (** Replace the current state. *)
  val put : T.t -> unit t

  (** Modify the current state. *)
  val modify : (T.t -> T.t) -> unit t

  (** Run the reader monad in some environment. *)
  val run : T.t -> 'a t -> 'a * T.t
end
