(* -------------------------------------------------------------------- *)
module Map    = BatMap
module Option = BatOption

(* -------------------------------------------------------------------- *)
module List : sig
  include module type of BatList

  type 'a pivot = 'a list * 'a * 'a list

  val pivot    : ('a -> bool) -> 'a list -> 'a pivot
  val pivoti   : (int -> 'a -> bool) -> 'a list -> 'a pivot
  val pivot_at : int -> 'a list -> 'a pivot
end = struct
  include BatList

  type 'a pivot = 'a list * 'a * 'a list

  let pivoti (f : int -> 'a -> bool) =
    let rec aux i pre s =
      match s with
      | [] -> invalid_arg "List.pivoti"
      | x :: s ->
          if f i x then
            (List.rev pre, x, s)
          else aux (i+1) (x :: pre) s
    in fun (s : 'a list) -> aux 0 [] s

  let pivot (f : 'a -> bool) (s : 'a list) =
    pivoti (fun _ -> f) s

  let pivot_at (i : int) (s : 'a list) =
    pivoti (fun j _ -> i = j) s
end

(* -------------------------------------------------------------------- *)
type uid = int

module Uid : sig
  val fresh : unit -> uid
end = struct
  let fresh () : uid =
    Oo.id (object end)
end

(* -------------------------------------------------------------------- *)
let curry   f (x, y) = f x y
let uncurry f x y = f (x, y)

let (^~) f = fun x y -> f y x

let (/>) (x : 'a option) (f : 'a -> 'b) =
  Option.map f x

let ueta (f : unit -> 'a) : 'b -> 'a =
  fun _ -> f ()
