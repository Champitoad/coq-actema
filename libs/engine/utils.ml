(* -------------------------------------------------------------------- *)
module Enum   = BatEnum
module Map    = BatMap
module Set    = BatSet
module UChar  = BatUChar
module UTF8   = BatUTF8

(* -------------------------------------------------------------------- *)
module Option : sig
  include module type of BatOption

  val fold : ('a -> 'b -> 'a) -> 'a -> 'b option -> 'a
end = struct
  include BatOption

  let fold f acc = function
    | None   -> acc
    | Some v -> f acc v
end

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
  let fresh : unit -> uid =     (* not mt-safe *)
    let count = ref (-1) in
    fun () -> incr count; !count
end

(* -------------------------------------------------------------------- *)
module Disposable : sig
  type 'a t

  exception Disposed

  val create  : ?cb:('a -> unit) -> 'a -> 'a t
  val get     : 'a t -> 'a
  val dispose : 'a t -> unit
end = struct
  type 'a t = ((('a -> unit) option * 'a) option) ref

  exception Disposed

  let get (p : 'a t) =
    match !p with
    | None -> raise Disposed
    | Some (_, x) -> x

  let dispose (p : 'a t) =
    let do_dispose p =
      match p with
      | Some (Some cb, x) -> cb x
      | _ -> ()
    in

    let oldp = !p in
      p := None; do_dispose oldp

  let create ?(cb : ('a -> unit) option) (x : 'a) =
    let r = ref (Some (cb, x)) in
    Gc.finalise (fun r -> dispose r) r; r
end

(* -------------------------------------------------------------------- *)
let fst_map f (x, y) = (f x, y)
let snd_map f (x, y) = (x, f y)

(* -------------------------------------------------------------------- *)
let curry   f (x, y) = f x y
let uncurry f x y = f (x, y)

let (^~) f = fun x y -> f y x

let (/>) (x : 'a option) (f : 'a -> 'b) =
  Option.map f x

let ueta (f : unit -> 'a) : 'b -> 'a =
  fun _ -> f ()
