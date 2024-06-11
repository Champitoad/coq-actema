(** This module implements bijections between finite sets i.e. bi-directional maps. 
    Author : Pablo Donato. *)

module type S = sig
  type key
  type value
  type t

  val bindings : t -> (key * value) list
  val of_list : (key * value) list -> t
  val keys : t -> key list
  val values : t -> value list
  val size : t -> int
  val empty : t
  val union : t -> t -> t
  val add : key -> value -> t -> t
  val replace : key -> value -> t -> t
  val remove : key -> t -> t
  val mem : key -> t -> bool
  val find : key -> t -> value
  val find_opt : key -> t -> value option
  val dnif : value -> t -> key
  val dnif_opt : value -> t -> key option
  val filter : (key -> value -> bool) -> t -> t
end

module Make (K : Map.OrderedType) (V : Map.OrderedType) :
  S with type key = K.t and type value = V.t
