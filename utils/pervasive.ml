(** This module implements miscelaneous utility functions. *)

include BatPervasives

(** [f >>> g] is left-to-right function composition : it applies [f] and then [g]. *)
let ( >>> ) f g x = g (f x)

(** [g <<< f] is right-to-left function composition : it applies [f] and then [g]. *)
let ( <<< ) g f x = g (f x)

(** Shorthands for batteries modules. *)

module Int = BatInt
module String = BatString
module Option = BatOption
module Seq = BatSeq
module Map = BatMap
module Set = BatSet

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
end
