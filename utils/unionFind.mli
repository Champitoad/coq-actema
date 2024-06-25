(** This module provides an implementation of partitions over finite sets,
    implemented as a union-find datastructure : 
    https://en.wikipedia.org/wiki/Disjoint-set_data_structure 
*)

(** Abstract inferface for a partition over elements of some type [elt]. 
    The partition is handled as a mutable data structure, but apart from
    this this interface does not constrain the implementation too much.
    
    All operations (except [add] and related operations) assume that the elements 
    have been previously added to the domain of the partition, and raise 
    an unspecified exception otherwise. 
*)
module type S = sig
  type elt

  (** The abstract type of a partition over elements of type [elt].
      Updates to the partition are done in place. *)
  type t

  (** Create an (empty) partition over an empty domain. *)
  val create : unit -> t

  (** [add p elt] adds the element [elt] to the partition [p]. 
      This also creates a new class that contains only [elt]. *)
  val add : t -> elt -> unit

  (** [of_list elts] creates a partition over a list of (pairwise distinct) 
      elements [elts], where each element is in its own class. *)
  val of_list : elt list -> t

  (** [domain p] returns the list of elements in the domain of the partition [p]. *)
  val domain : t -> elt list

  (** [find p elt] returns the representative of the class of [elt] in the partition [p]. 
      This may update the partition in place. *)
  val find : t -> elt -> elt

  (** [union p elt1 elt2] merges the classes of [elt1] and [elt2] in the partition [p]. 
      This may update the partition in place. *)
  val union : t -> elt -> elt -> unit

  (** [equiv p elt1 elt2] returns [true] if and only if [elt1] and [elt2] are in the same 
      class in the partition [p]. This may update the partition in place. *)
  val equiv : t -> elt -> elt -> bool

  (** [is_representative p elt] returns [true] if and only if [elt] is the representative
      of its class in the partition [p]. *)
  val is_representative : t -> elt -> bool
end

(** A union-find datastructure which uses hashtables internally. 
    The provided element type has to be hashable.
    The implementation uses path compression and union by rank to provide good performance. 
*)
module Make (Elt : Hashtbl.HashedType) : S with type elt = Elt.t
