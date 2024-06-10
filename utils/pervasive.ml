(** This module implements miscelaneous utility functions. *)

include BatPervasives

(** [f >>> g] is left-to-right function composition : it applies [f] and then [g]. *)
let ( >>> ) f g x = g (f x)

(** [g <<< f] is right-to-left function composition : it applies [f] and then [g]. *)
let ( <<< ) g f x = g (f x)

(** [indices ?start=0 [x0; x1; ... xn]] returns the list [(start, x0); (start+1; x1); ... (start+n, xn)]. *)
let indices ?(start = 0) xs = List.mapi (fun i x -> (start + i, x)) xs

(** [pair_map f (a, b) = (f a, f b)]. *)
let pair_map f (a, b) = (f a, f b)

(** [pair_compare comp1 comp2] implements lexicographic comparison on pairs ['a * 'b] 
    (in the sense of Stdlib.Compare), assuming comparison functions [comp1] on ['a] and [comp2] on ['b]. *)
let pair_compare comp1 comp2 ((a1, b1) : 'a * 'b) ((a2, b2) : 'a * 'b) : int =
  match comp1 a1 a2 with 0 -> comp2 b1 b2 | n -> n

(** Same as [pair_compare] but for triples. *)
let triple_compare comp1 comp2 comp3 ((a1, b1, c1) : 'a * 'b * 'c)
    ((a2, b2, c2) : 'a * 'b * 'c) : int =
  match comp1 a1 a2 with
  | 0 -> begin match comp2 b1 b2 with 0 -> comp3 c1 c2 | n -> n end
  | n -> n

(** [lex_compare comp] implements lexicographic comparison on list ['a list] 
    (in the sense of Stdlib.Compare), assuming a comparison function [comp] on ['a]. *)
let lex_compare comp (xs : 'a list) (ys : 'a list) : int =
  let rec loop xs ys =
    match (xs, ys) with
    | [], [] -> 0
    | [], _ :: _ -> -1
    | _ :: _, [] -> 1
    | x :: xs, y :: ys -> begin
        match comp x y with 0 -> loop xs ys | n -> n
      end
  in
  loop xs ys

(** Shorthands for batteries modules. *)

module Int = BatInt
module String = BatString
module Option = BatOption
module Seq = BatSeq
module Map = BatMap
module Set = BatSet
module Enum = BatEnum

(** Instantiate modules to some common types. *)

module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)

(** More functions on lists. *)

module List = struct
  include BatList

  (** [is_prefix xs ys] tests whether [xs] is a prefix of [ys]. *)
  let rec is_prefix (xs : 'a list) (ys : 'a list) : bool =
    match (xs, ys) with
    | [], _ -> true
    | x :: xs, y :: ys -> x = y && is_prefix xs ys
    | _ -> false

  let to_string ?(sep = "; ") ?(left = "[") ?(right = "]") print =
    List.map print >>> String.join sep >>> fun s -> left ^ s ^ right

  (** [find_max f xs] finds the element [x] of [xs] that has the largest value when mapped by [f].
      Returns [None] if [xs] is empty. *)
  let find_max (f : 'a -> 'b) (xs : 'a list) : 'a option =
    let rec loop x_max = function
      | [] -> x_max
      | hd :: tl when f x_max < f hd -> loop hd tl
      | hd :: tl -> loop x_max tl
    in
    match xs with [] -> None | x :: xs -> Some (loop x xs)
end

(** Names : wrappers around strings. *)

module Name : sig
  (** A name is essentially a wrapper around a string, but provides more efficient comparison functions 
    by hashing the string. Names are used pervasively in Actema so we provide an efficient and
    encapsulated implementation. *)
  type t [@@deriving show]

  (** Create a variable with the given name. This is a pure function. *)
  val make : string -> t

  (** Compare variables efficiently. *)
  val compare : t -> t -> int

  (** Test for equality between variables efficiently. *)
  val equal : t -> t -> bool

  (** Get the hash of the name. This is O(1). *)
  val hash : t -> int

  (** A few modules on Names. *)

  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t
  module Hashtbl : Hashtbl.S with type key = t
end = struct
  type t = { str : string; hsh : int }

  let show name = name.str
  let pp fmt name = Format.fprintf fmt "%s" name.str

  (** We compute the hash of [str] once and forall, and reuse it later. *)
  let make str = { str; hsh = Hashtbl.hash str }

  let hash name = name.hsh
  let equal n1 n2 = n1.hsh = n2.hsh && n1.str = n2.str
  let compare n1 n2 = compare n1 n2

  module Set = Set.Make (struct
    type nonrec t = t

    let compare = compare
  end)

  module Map = Map.Make (struct
    type nonrec t = t

    let compare = compare
  end)

  module Hashtbl = Hashtbl.Make (struct
    type nonrec t = t

    let hash = hash
    let equal = equal
  end)
end
