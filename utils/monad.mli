(** This module implements some basic but very useful monads. 
    
    There is nothing fancy going on here, in particular no monad transformers
    (although they could be added in the future). 
    
    Author : Mathis Bouverot-Dupuis. *)

(**************************************************************************************)

(** The signature for a standard monad. *)
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

  (** Infix [map]. *)
  val ( <$> ) : ('a -> 'b) -> 'a t -> 'b t

  (** Applicative stuff. *)
  val ( <*> ) : ('a -> 'b) t -> 'a t -> 'b t

  (** Infix [bind]. *)
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t

  (** Reversed infix [bind]. *)
  val ( =<< ) : ('a -> 'b t) -> 'a t -> 'b t

  (** Infix [bind] that doesn't use its argument. *)
  val ( >> ) : 'a t -> 'b t -> 'b t

  (** Reversed infix [bind] that doesn't use its argument. *)
  val ( << ) : 'a t -> 'b t -> 'a t

  (** Let-style [map]. *)
  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t

  (** Let-style [bind]. *)
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t

  (** Sequence a list of monadic actions, one after the other. *)
  val sequence : 'a t list -> 'a list t

  (** Repeat a monadic action a given number of times, then [sequence] the actions.
      If the count is [< 0] this simply returns the empty list. *)
  val repeatM : int -> 'a t -> 'a list t

  (** Map a monadic action over a list. *)
  val mapM : ('a -> 'b t) -> 'a list -> 'b list t

  (** Same as [mapM], but discards the result. *)
  val mapM_ : ('a -> 'b t) -> 'a list -> unit t

  (** Fold a monadic action over a list. *)
  val foldM : ('acc -> 'a -> 'acc t) -> 'acc -> 'a list -> 'acc t
end

(** The signature for a monad that is also a monoid.
    For instance lists and options satisfy this interface. *)
module type SPlus = sig
  include S

  (** The monoid identity. This generalizes [List.nil]. *)
  val mzero : 'a t

  (** The monoid (associative) operation. This generalizes [List.append]. *)
  val mplus : 'a t -> 'a t -> 'a t

  (** Infix [mplus]. *)
  val ( <|> ) : 'a t -> 'a t -> 'a t

  (** Take the sum of a list of monadic values. This generalizes [List.concat]. *)
  val msum : 'a t list -> 'a t

  (** Contional failure. It is defined by [guard true = return ()] and [guard false = mzero]. *)
  val guard : bool -> unit t
end

(**************************************************************************************)

(** Make a monad from a minimal set of operations. *)
module Make (M : sig
  type 'a t

  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end) : S with type 'a t = 'a M.t

(** Make a monad-plus from a minimal set of operations. *)
module MakePlus (M : sig
  type 'a t

  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val mzero : 'a t
  val mplus : 'a t -> 'a t -> 'a t
end) : SPlus with type 'a t = 'a M.t

(**************************************************************************************)
(** Some useful monads. *)

(** Standard option monad. *)
module Option : SPlus with type 'a t = 'a option

(** Standard list monad. *)
module List : SPlus with type 'a t = 'a list

(** Lazy list monad. *)
module Seq : SPlus with type 'a t = 'a Seq.t

(** Standard reader monad over some type [T.t].
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

(** Standard state monad over some type [T.t].
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
