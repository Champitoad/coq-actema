val identity : 'a -> 'a
val ( |>> ) : ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c
val ( <<| ) : ('b -> 'c) -> ('a -> 'b) -> 'a -> 'c

module BiMap (K : Map.OrderedType) (V : Map.OrderedType) : sig
  type t

  val bindings : t -> (K.t * V.t) list
  val of_list : (K.t * V.t) list -> t
  val keys : t -> K.t list
  val values : t -> V.t list
  val size : t -> int
  val empty : t
  val union : t -> t -> t
  val add : K.t -> V.t -> t -> t
  val replace : K.t -> V.t -> t -> t
  val remove : K.t -> t -> t
  val mem : K.t -> t -> bool
  val find : K.t -> t -> V.t
  val find_opt : K.t -> t -> V.t option
  val dnif : V.t -> t -> K.t
  val dnif_opt : V.t -> t -> K.t option
  val filter : (K.t -> V.t -> bool) -> t -> t
end

module List : sig
  include module type of Stdlib.List

  val nth_index : int -> 'a -> 'a t -> int
  val to_string : ?sep:string -> ?left:string -> ?right:string -> ('a -> string) -> 'a t -> string

  (** Returns the first [n] elements of a list [l]. 
      If [l] has less than [n] elements, returns [l]. *)
  val take : int -> 'a list -> 'a list

  (** Like [cons], but in reverse. *)
  val snoc : 'a list -> 'a -> 'a list

  (** The opposite of [snoc] : seperate a list into its last element and the initial portion. *)
  val unsnoc : 'a list -> ('a list * 'a) option

  (** Get the last element of a list. Raises [Failure] if the list is empty. *)
  val last : 'a list -> 'a
end

val ssystime : unit -> string

(** Execute a function and return the execution time in seconds. *)
val time : (unit -> 'a) -> unit -> 'a * float
