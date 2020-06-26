(* -------------------------------------------------------------------- *)
module Enum   = BatEnum
module Map    = BatMap
module Set    = BatSet
module UChar  = BatUChar
module UTF8   = BatUTF8
module BIO    = BatIO
module Lexing = BatLexing
module String = BatString

include BatPervasives

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
let uc f (x, y) = f x y

(* -------------------------------------------------------------------- *)
module List : sig
  include module type of BatList

  val ns : int -> int list

  val fst : ('a * 'b) list -> 'a list
  val snd : ('a * 'b) list -> 'b list

  val pop_assoc : 'a -> ('a * 'b) list -> ('a * 'b) list * 'b

  val findex : ('a -> bool) -> 'a list -> int option
  val join   : 'a -> 'a list -> 'a list

  type 'a pivot = 'a list * 'a * 'a list

  val of_option : 'a option -> 'a list
  val pivot     : ('a -> bool) -> 'a list -> 'a pivot
  val pivoti    : (int -> 'a -> bool) -> 'a list -> 'a pivot
  val pivot_at  : int -> 'a list -> 'a pivot

  exception TopoFailure

  val topo : ('a -> int) -> ('a -> int list) -> 'a list -> 'a list
end = struct
  include BatList

  let ns n = List.init n (fun i -> i)

  let fst xs = List.map fst xs
  let snd xs = List.map snd xs

  let pop_assoc a l =
    let rec aux acc a = function
      | [] -> raise Not_found
      | (b, x) :: l when a = b -> (List.rev acc) @ l, x
      | i :: l -> aux (i :: acc) a l
    in aux [] a l

  let findex (type a) (check : a -> bool) (xs : a list) : int option =
    match Exceptionless.findi (fun _ x -> check x) xs with
    | None -> None | Some (i, _) -> Some i

  let join (sep : 'a) =
    let rec doit acc xs =
      match xs with
      | [] -> List.rev acc
      | x :: xs -> doit (x :: sep :: acc) xs
    in function ([] | [_]) as xs -> xs | x :: xs -> doit [x] xs

  type 'a pivot = 'a list * 'a * 'a list

  let of_option (x : 'a option) : 'a list =
    match x with None -> [] | Some x -> [x]

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

  exception TopoFailure

  let topo (type a) (key : a -> int) (deps : a -> int list) =
    let rec aux acc later todo progress =
      match todo, later with
      | [], [] ->
          List.rev acc

      | [], _ ->
          if not progress then raise TopoFailure;
          aux acc [] later false

      | x::xs, _ ->
        let ok =
          List.for_all
            (fun dep -> exists (fun y -> key y = dep) acc)
            (deps x) in

        if   ok
        then aux (x::acc) later xs true
        else aux acc (x::later) xs progress
    in

    fun (xs : a list) ->
      let starts, todo =
        List.partition (fun x -> is_empty (deps x)) xs
      in aux starts [] todo false
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

let (|>>) f g = fun x -> g (f x)
let (<<|) f g = fun x -> f (g x)

let (^~) f = fun x y -> f y x

let (/>) (x : 'a option) (f : 'a -> 'b) =
  Option.map f x

let ueta (f : unit -> 'a) : 'b -> 'a =
  fun _ -> f ()
