open QCheck2

include Monad.Make (struct
  type nonrec 'a t = 'a option Gen.t

  let return x = Gen.return (Some x)

  let bind a f =
    Gen.bind a @@ function None -> Gen.return None | Some a -> f a
end)

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
