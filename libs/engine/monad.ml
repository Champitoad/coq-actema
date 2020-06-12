
(** Useful monads *)

open Utils

module type Type = sig type t end

(** Basic monad *)

module type Core = sig
  type 'a t
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
end

(** Basic monad with an additional monoid structure *)

module type Plus = sig
  include Core
  val zero : 'a t
  val ( + ) : 'a t -> 'a t -> 'a t
end

(** Basic monad with an additional environment type *)

module type Env = sig
  include Core
  type env
end

(** Reader monad to carry some environment in read-only mode *)

module Reader (T : Type) : sig
  include Env with type 'a t = T.t -> 'a

  (* Monadic version of List.map *)
  val map : ('a -> 'b t) -> 'a list -> 'b list t
end = struct
  type env = T.t
  type 'a t = env -> 'a
  let return x = fun st -> x
  let bind m f = fun st -> f (m st) st
  let ( >>= ) = bind
  let map f l = fun st ->
    List.map (fun x -> f x st) l
end

(** State monad to carry some environment in read-write mode *)

module State (T : Type) : sig
  include Env with type 'a t = T.t -> 'a * T.t

  (* Monadic version of List.iter *)
  val iter : ('a -> 'b t) -> 'a list -> unit t

  val run : 'a t -> T.t -> 'a
end = struct
  type env = T.t
  type 'a t = env -> 'a * env
  let return x = fun st -> x, st
  let bind m f = fun st ->
    let x, st' = m st in
    f x st'
  let ( >>= ) = bind
  let iter f l = fun st ->
    (), List.fold_left
      (fun st x -> (f x |>> snd) st)
      st l
  let run m = m |>> fst
end

(** List monad to implement list comprehension *)

module List : Plus
  with type 'a t = 'a list =
struct
  type 'a t = 'a list
  let return x = [x]
  let bind m f = List.concat_map f m
  let ( >>= ) = bind
  let zero = []
  let ( + ) = ( @ )
end