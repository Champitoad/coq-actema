(**************************************************************************************)

module type S = sig
  type 'a t

  val return : 'a -> 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
  val join : 'a t t -> 'a t
  val ( <$> ) : ('a -> 'b) -> 'a t -> 'b t
  val ( <*> ) : ('a -> 'b) t -> 'a t -> 'b t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( =<< ) : ('a -> 'b t) -> 'a t -> 'b t
  val ( >> ) : 'a t -> 'b t -> 'b t
  val ( << ) : 'a t -> 'b t -> 'a t
  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val sequence : 'a t list -> 'a list t
  val mapM : ('a -> 'b t) -> 'a list -> 'b list t
  val mapM_ : ('a -> 'b t) -> 'a list -> unit t
  val foldM : ('acc -> 'a -> 'acc t) -> 'acc -> 'a list -> 'acc t
end

(**************************************************************************************)

module Make (M : sig
  type 'a t

  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end) =
struct
  type 'a t = 'a M.t

  let return = M.return
  let bind = M.bind
  let ( >>= ) = bind
  let ( =<< ) f x = bind x f
  let ( let* ) = bind

  let map f x =
    let* a = x in
    return @@ f a

  let ( >> ) x y = x >>= fun _ -> y
  let ( << ) y x = x >>= fun _ -> y
  let ( <$> ) = map

  let ( <*> ) mf m =
    let* f = mf in
    let* x = m in
    return (f x)

  let ( let+ ) x f = map f x
  let join x = x >>= Fun.id

  let rec sequence ms =
    match ms with [] -> return [] | m :: ms -> List.cons <$> m <*> sequence ms

  let mapM f xs = sequence @@ List.map f xs

  let mapM_ f xs =
    let+ _ = mapM f xs in
    ()

  let foldM f acc xs =
    List.fold_left
      (fun acc x ->
        let* acc = acc in
        f acc x)
      (return acc) xs
end

(**************************************************************************************)

module Option = Make (struct
  type 'a t = 'a option

  let return x = Some x
  let bind = Option.bind
end)

module List = Make (struct
  type 'a t = 'a list

  let return x = [ x ]
  let bind x f = List.concat_map f x
end)

module Seq = Make (struct
  type 'a t = 'a Seq.t

  let return x = Seq.cons x Seq.empty
  let bind x f = Seq.concat_map f x
end)

module Reader (T : sig
  type t
end) =
struct
  include Make (struct
    type 'a t = T.t -> 'a

    let return x env = x
    let bind x f env = f (x env) env
  end)

  let get env = env
  let run env x = x env
end

module State (T : sig
  type t
end) =
struct
  include Make (struct
    type 'a t = T.t -> 'a * T.t

    let return x state = (x, state)

    let bind x f state =
      let x, state = x state in
      f x state
  end)

  let get state = (state, state)
  let put state _ = ((), state)
  let modify f state = ((), f state)
  let run state x = x state
end
