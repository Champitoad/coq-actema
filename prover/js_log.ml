(** This module will log messages to the Javascript console. 

    You should use this module instead of [Format] or [Printf] to log
    messages from the prover (or else the messages might not get displayed). *)

open Js_of_ocaml

(** Print an (Ocaml) string. A newline is added automatically. *)
let log (s : string) : unit = Firebug.console##log (Js.string s)

(** Same as [log], but logs an arbitrary javascript object. *)
let log_object (obj : 'a Js.t) : unit = Firebug.console##log obj

(* -------------------------------------------------------------------- *)
(*module Enum = BatEnum
  module Map = BatMap
  module Set = BatSet
  module UChar = BatUChar
  module UTF8 = BatUTF8
  module BIO = BatIO
  module Lexing = BatLexing
  module String = BatString
  include BatPervasives
  module IntSet = Set.Make (Int)
  module IntMap = Map.Make (Int)

  (* -------------------------------------------------------------------- *)


  (** Time the execution of a function and print the measured duration. *)
  let time (label : string) (f : unit -> 'a) : 'a =
    let start = Sys.time () in
    let res = f () in
    let stop = Sys.time () in
    js_log @@ Format.sprintf "Time [%s]: %.2f seconds\n" label (stop -. start);
    res

  (* -------------------------------------------------------------------- *)

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
  module Option = struct
    include BatOption

    let fold f acc = function None -> acc | Some v -> f acc v
    let to_string pp = map_default pp "None"

    module Syntax = struct
      let ( <$> ) = Option.map
      let ( let+ ) = Option.map
      let ( >>= ) = Option.bind
      let ( let* ) = Option.bind

      let foldM (f : 'acc -> 'a -> 'acc option) (acc : 'acc) (xs : 'a list) :
          'acc option =
        List.fold_left
          (fun acc x -> match acc with None -> None | Some acc -> f acc x)
          (Some acc) xs
    end
  end

  (* -------------------------------------------------------------------- *)
  (*module List : sig
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
        match Exceptionless.findi (fun _ x -> check x) xs with
        | None -> None
        | Some (i, _) -> Some i

      let join (sep : 'a) =
        let rec doit acc xs =
          match xs with [] -> List.rev acc | x :: xs -> doit (x :: sep :: acc) xs
        in
        function ([] | [ _ ]) as xs -> xs | x :: xs -> doit [ x ] xs

      type 'a pivot = 'a list * 'a * 'a list

      let of_option (x : 'a option) : 'a list =
        match x with None -> [] | Some x -> [ x ]

      let pivoti (f : int -> 'a -> bool) =
        let rec aux i pre s =
          match s with
          | [] -> invalid_arg "List.pivoti"
          | x :: s ->
              if f i x then (List.rev pre, x, s) else aux (i + 1) (x :: pre) s
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
              let ok =
                List.for_all (fun dep -> exists (fun y -> key y = dep) acc) (deps x)
              in

              if ok
              then aux (x :: acc) later xs true
              else aux acc (x :: later) xs progress
        in

        fun (xs : a list) ->
          let starts, todo = List.partition (fun x -> is_empty (deps x)) xs in
          aux starts [] todo false

      let find_map_opt (f : 'a -> 'b option) =
        let rec doit xs =
          match xs with
          | [] -> None
          | x :: xs -> ( match f x with None -> doit xs | Some v -> Some v)
        in
        fun xs -> doit xs
    end*)
*)
