open Batteries
module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)
module StringMap = Map.Make (String)

module BGen = struct
  open QCheck2

  type 'a t = 'a option Gen.t

  let return x = Gen.return (Some x)
  let map f a = Gen.map (Option.map f) a

  let bind a f =
    Gen.bind a @@ function None -> Gen.return None | Some a -> f a

  let fail () = Gen.return None
  let guard c a = bind a @@ fun a -> if c a then return a else fail ()
  let cond c a = if c then a else fail ()
  let lift gen = Gen.bind gen @@ fun res -> return res

  let rec run a =
    Gen.bind a @@ function Some res -> Gen.return res | None -> run a

  let run_opt a = a

  let rec first (gens : 'a t list) : 'a t =
    match gens with
    | [] -> fail ()
    | g :: gens ->
        Gen.bind g (function None -> first gens | Some res -> return res)

  let oneof gens =
    (* Shuffle the order of the generators, and then get the first one that succeeds. *)
    Gen.bind (Gen.shuffle_l gens) first

  let oneofl xs = if List.is_empty xs then fail () else lift (Gen.oneofl xs)
  let frequency weighted_gens = Gen.bind (Gen.shuffle_w_l weighted_gens) first

  module Syntax = struct
    let ( let+ ) a f = map f a
    let ( <$> ) = map
    let ( let* ) = bind

    let ( <*> ) f a =
      let* f = f in
      let* a = a in
      return (f a)

    let ( >>= ) = bind
    let ( =<< ) f a = bind a f
  end
end

module BiMap = struct
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
    let r =
      r1 |> Map.filter (fun k _ -> not (Map.exists (fun k' _ -> k = k') r2))
    in
    let l = r |> Map.enum |> Enum.map (fun (x, y) -> (y, x)) |> Map.of_enum in
    (r, l)

  let vdiff (_, l1) (_, l2) =
    let l =
      l1 |> Map.filter (fun k _ -> not (Map.exists (fun k' _ -> k = k') l2))
    in
    let r = l |> Map.enum |> Enum.map (fun (x, y) -> (y, x)) |> Map.of_enum in
    (r, l)

  let of_enum e =
    (Map.of_enum e, Map.of_enum (e |> Enum.map (fun (x, y) -> (y, x))))

  let of_seq s = (Map.of_seq s, Map.of_seq (s |> Seq.map (fun (x, y) -> (y, x))))
end
