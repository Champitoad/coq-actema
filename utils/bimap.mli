(** This module implements bijections between finite sets, i.e. bi-directional maps. 
    Implemented by Pablo Donato. *)

module Make (K : Map.OrderedType) (V : Map.OrderedType) : sig
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
