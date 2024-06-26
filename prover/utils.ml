(* -------------------------------------------------------------------- *)
module Enum = BatEnum
module Map = BatMap
module Set = BatSet
module UChar = BatUChar
module UTF8 = BatUTF8
module BIO = BatIO
module Lexing = BatLexing
module String = BatString
include BatPervasives

(* -------------------------------------------------------------------- *)

let js_log s = Js_of_ocaml.(Firebug.console##log (Js.string s))

(** Time the execution of a function and print the measured duration. *)
let time (label : string) (f : unit -> 'a) : 'a =
  let start = Sys.time () in
  let res = f () in
  let stop = Sys.time () in
  js_log @@ Format.sprintf "Time [%s]: %.2f seconds\n" label (stop -. start);
  res

(* -------------------------------------------------------------------- *)

(** You should use this instead of Format.printf or Printf.printf to log
    messages from the prover (or else the messages might not get displayed). *)
let fst_map f (x, y) = (f x, y)

let snd_map f (x, y) = (x, f y)
let pair_map f (x, y) = (f x, f y)

(* -------------------------------------------------------------------- *)
let ( |>> ) f g x = g (f x)
let ( <<| ) f g x = f (g x)
let curry f (x, y) = f x y
let uncurry f x y = f (x, y)
let ( ^~ ) f x y = f y x
let ( /> ) (x : 'a option) (f : 'a -> 'b) = BatOption.map f x
let ueta (f : unit -> 'a) : 'b -> 'a = fun _ -> f ()

(* -------------------------------------------------------------------- *)
module Option : sig
  include module type of BatOption

  val fold : ('a -> 'b -> 'a) -> 'a -> 'b option -> 'a
  val to_string : ('a -> string) -> 'a option -> string
end = struct
  include BatOption

  let fold f acc = function None -> acc | Some v -> f acc v
  let to_string pp = map_default pp "None"
end

(* -------------------------------------------------------------------- *)
module List : sig
  include module type of BatList

  val ns : int -> int list
  val fst : ('a * 'b) list -> 'a list
  val snd : ('a * 'b) list -> 'b list
  val pop_at : int -> 'a list -> 'a * 'a list
  val pop_assoc : 'a -> ('a * 'b) list -> ('a * 'b) list * 'b
  val findex : ('a -> bool) -> 'a list -> int option
  val join : 'a -> 'a list -> 'a list

  type 'a pivot = 'a list * 'a * 'a list

  val of_option : 'a option -> 'a list
  val pivot : ('a -> bool) -> 'a list -> 'a pivot
  val pivoti : (int -> 'a -> bool) -> 'a list -> 'a pivot
  val pivot_at : int -> 'a list -> 'a pivot

  exception TopoFailure

  val topo : ('a -> int) -> ('a -> int list) -> 'a list -> 'a list
  val find_map_opt : ('a -> 'b option) -> 'a list -> 'b option
  val is_prefix : 'a list -> 'a list -> bool

  val to_string :
    ?sep:string -> ?left:string -> ?right:string -> ('a -> string) -> 'a list -> string
end = struct
  include BatList

  let ns n = List.init n (fun i -> i)
  let fst xs = List.map fst xs
  let snd xs = List.map snd xs

  let pop_at i l =
    let rec aux acc i l =
      match (i, l) with
      | 0, x :: l -> (x, List.rev_append acc l)
      | _, x :: l -> aux (x :: acc) (i - 1) l
      | _ -> raise Not_found
    in
    aux [] i l

  let pop_assoc a l =
    let rec aux acc a = function
      | [] -> raise Not_found
      | (b, x) :: l when a = b -> (List.rev_append acc l, x)
      | i :: l -> aux (i :: acc) a l
    in
    aux [] a l

  let findex (type a) (check : a -> bool) (xs : a list) : int option =
    match Exceptionless.findi (fun _ x -> check x) xs with None -> None | Some (i, _) -> Some i

  let join (sep : 'a) =
    let rec doit acc xs =
      match xs with [] -> List.rev acc | x :: xs -> doit (x :: sep :: acc) xs
    in
    function ([] | [ _ ]) as xs -> xs | x :: xs -> doit [ x ] xs

  type 'a pivot = 'a list * 'a * 'a list

  let of_option (x : 'a option) : 'a list = match x with None -> [] | Some x -> [ x ]

  let pivoti (f : int -> 'a -> bool) =
    let rec aux i pre s =
      match s with
      | [] -> invalid_arg "List.pivoti"
      | x :: s -> if f i x then (List.rev pre, x, s) else aux (i + 1) (x :: pre) s
    in
    fun (s : 'a list) -> aux 0 [] s

  let pivot (f : 'a -> bool) (s : 'a list) = pivoti (fun _ -> f) s
  let pivot_at (i : int) (s : 'a list) = pivoti (fun j _ -> i = j) s

  exception TopoFailure

  let topo (type a) (key : a -> int) (deps : a -> int list) =
    let rec aux acc later todo progress =
      match (todo, later) with
      | [], [] -> List.rev acc
      | [], _ ->
          if not progress then raise TopoFailure;
          aux acc [] later false
      | x :: xs, _ ->
          let ok = List.for_all (fun dep -> exists (fun y -> key y = dep) acc) (deps x) in

          if ok then aux (x :: acc) later xs true else aux acc (x :: later) xs progress
    in

    fun (xs : a list) ->
      let starts, todo = List.partition (fun x -> is_empty (deps x)) xs in
      aux starts [] todo false

  let find_map_opt (f : 'a -> 'b option) =
    let rec doit xs =
      match xs with [] -> None | x :: xs -> ( match f x with None -> doit xs | Some v -> Some v)
    in
    fun xs -> doit xs

  let rec is_prefix (xs : 'a list) (pr : 'a list) =
    match (xs, pr) with
    | _, [] -> true
    | x :: xs, y :: pr -> x = y && is_prefix xs pr
    | _, _ -> false

  let to_string ?(sep = "; ") ?(left = "[") ?(right = "]") print =
    List.map print |>> String.join sep |>> fun s -> left ^ s ^ right
end

(* -------------------------------------------------------------------- *)
module BiMap : sig
  type ('a, 'b) t

  val bindings : ('a, 'b) t -> ('a * 'b) list
  val empty : ('a, 'b) t
  val inverse : ('a, 'b) t -> ('b, 'a) t
  val add : 'a -> 'b -> ('a, 'b) t -> ('a, 'b) t
  val remove : 'a -> ('a, 'b) t -> ('a, 'b) t
  val union : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
  val find : 'a -> ('a, 'b) t -> 'b
  val find_opt : 'a -> ('a, 'b) t -> 'b option
  val domain : ('a, 'b) t -> 'a list
  val codomain : ('a, 'b) t -> 'b list
  val kdiff : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
  val vdiff : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t
  val of_enum : ('a * 'b) Enum.t -> ('a, 'b) t
  val of_seq : ('a * 'b) Seq.t -> ('a, 'b) t
end = struct
  type ('a, 'b) t = ('a, 'b) Map.t * ('b, 'a) Map.t

  let bindings (r, _) = Map.bindings r
  let empty = (Map.empty, Map.empty)
  let inverse (r, l) = (l, r)
  let add k v (r, l) = (Map.add k v r, Map.add v k l)

  let remove k (r, l) =
    let v = Map.find k r in
    (Map.remove k r, Map.remove v l)

  let union (r1, l1) (r2, l2) = (Map.union r1 r2, Map.union l1 l2)
  let find k (r, _) = Map.find k r
  let find_opt k (r, _) = Map.find_opt k r
  let domain (r, _) = Map.keys r |> List.of_enum
  let codomain (_, l) = Map.keys l |> List.of_enum

  let kdiff (r1, _) (r2, _) =
    let r = r1 |> Map.filter (fun k _ -> not (Map.exists (fun k' _ -> k = k') r2)) in
    let l = r |> Map.enum |> Enum.map (fun (x, y) -> (y, x)) |> Map.of_enum in
    (r, l)

  let vdiff (_, l1) (_, l2) =
    let l = l1 |> Map.filter (fun k _ -> not (Map.exists (fun k' _ -> k = k') l2)) in
    let r = l |> Map.enum |> Enum.map (fun (x, y) -> (y, x)) |> Map.of_enum in
    (r, l)

  let of_enum e = (Map.of_enum e, Map.of_enum (e |> Enum.map (fun (x, y) -> (y, x))))
  let of_seq s = (Map.of_seq s, Map.of_seq (s |> Seq.map (fun (x, y) -> (y, x))))
end

(* -------------------------------------------------------------------- *)
type uid = int

module Uid : sig
  include Map.OrderedType

  val fresh : unit -> uid
end
with type t = int = struct
  type t = int

  let compare = Int.compare

  let fresh : unit -> uid =
    (* not mt-safe *)
    let count = ref (-1) in
    fun () ->
      incr count;
      !count
end

(* -------------------------------------------------------------------- *)
module Disposable : sig
  type 'a t

  exception Disposed

  val create : ?cb:('a -> unit) -> 'a -> 'a t
  val get : 'a t -> 'a
  val dispose : 'a t -> unit
end = struct
  type 'a t = (('a -> unit) option * 'a) option ref

  exception Disposed

  let get (p : 'a t) = match !p with None -> raise Disposed | Some (_, x) -> x

  let dispose (p : 'a t) =
    let do_dispose p = match p with Some (Some cb, x) -> cb x | _ -> () in

    let oldp = !p in
    p := None;
    do_dispose oldp

  let create ?(cb : ('a -> unit) option) (x : 'a) =
    let r = ref (Some (cb, x)) in
    Gc.finalise (fun r -> dispose r) r;
    r
end

(* -------------------------------------------------------------------- *)

module Text : sig
  val spaced : ?left:bool -> ?right:bool -> string -> string
  val pr : ?doit:bool -> string -> string
end = struct
  let pr ?(doit = true) c = if doit then Format.sprintf "(%s)" c else c

  let spaced ?(left = true) ?(right = true) c =
    Format.sprintf "%s%s%s" (if left then " " else "") c (if right then " " else "")
end

open Tyxml

module Html : sig
  val span : ?a:Xml.attrib list -> Xml.elt list -> Xml.elt
  val spaced : ?left:bool -> ?right:bool -> Xml.elt list -> Xml.elt list
  val pr : ?doit:bool -> Xml.elt list -> Xml.elt list
end = struct
  let span ?a = Xml.node ?a "span"

  let spaced ?(left = true) ?(right = true) c =
    let sp = [ span [ Xml.entity "nbsp" ] ] in
    let c = if left then sp @ c else c in
    let c = if right then c @ sp else c in
    c

  let pr ?(doit = true) c =
    let l = [ span [ Xml.pcdata "(" ] ] in
    let r = [ span [ Xml.pcdata ")" ] ] in
    if doit then l @ c @ r else c
end

module Mathml : sig
  val math : ?a:Xml.attrib list -> Xml.elt list -> Xml.elt
  val row : ?a:Xml.attrib list -> Xml.elt list -> Xml.elt
  val mo : string -> Xml.elt
  val mi : string -> Xml.elt
  val mn : string -> Xml.elt
  val spaced : ?left:bool -> ?right:bool -> Xml.elt list -> Xml.elt list
  val pr : ?doit:bool -> Xml.elt -> Xml.elt
end = struct
  let math ?a = Xml.node ?a "math"
  let row ?a = Xml.node ?a "mrow"
  let mo c = Xml.node "mo" [ Xml.pcdata c ]
  let mi c = Xml.node "mi" [ Xml.pcdata c ]
  let mn c = Xml.node "mn" [ Xml.pcdata c ]

  let spaced ?(left = true) ?(right = true) c =
    let sp = [ Xml.node "mo" [ Xml.entity "nbsp" ] ] in
    let c = if left then sp @ c else c in
    let c = if right then c @ sp else c in
    c

  let pr ?(doit = true) c = if doit then row [ mo "("; c; mo ")" ] else c
end
