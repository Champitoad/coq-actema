module BiMap (K : Map.OrderedType) (V : Map.OrderedType) : sig
  type t

  val bindings : t -> (K.t * V.t) list
  val of_list : (K.t * V.t) list -> t
  val keys : t -> K.t list
  val values : t -> V.t list
  val size : t -> int

  val empty : t
  val add : K.t -> V.t -> t -> t
  val replace : K.t -> V.t -> t -> t
  val remove : K.t -> t -> t

  val find : K.t -> t -> V.t
  val find_opt : K.t -> t -> V.t option
  val dnif : V.t -> t -> K.t
  val dnif_opt : V.t -> t -> K.t option
end

module List : sig
  include module type of Stdlib.List

  val nth_index : int -> 'a -> 'a t -> int
end