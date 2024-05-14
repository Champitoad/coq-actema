(***************************************************************************************)
(** Names *)

module Name = struct
  type t = { str : string; hsh : int } [@@deriving show]

  let show name = name.str
  let pp fmt name = Format.fprintf fmt "%s" name.str

  (** We compute the hash of [str] once and forall, and reuse it later. *)
  let make str = { str; hsh = Hashtbl.hash str }

  let hash name = name.hsh
  let equal n1 n2 = n1.hsh = n2.hsh && n1.str = n2.str
  let compare n1 n2 = compare n1 n2

  module Map = Map.Make (struct
    type nonrec t = t

    let compare = compare
  end)

  module Hashtbl = Hashtbl.Make (struct
    type nonrec t = t

    let hash = hash
    let equal = equal
  end)

  (** We use a special symbol [!] to ensure this is distinct from any Coq identifiers. *)
  let dummy = make "!dummy"

  let and_ = make "Coq.Init.Logic.and"
  let or_ = make "Coq.Init.Logic.or"
end

(***************************************************************************************)
(** Terms *)

module Term = struct
  type t =
    | Var of Name.t
    | App of t * t list
    | Lambda of Name.t * t * t
    | Arrow of t * t
    | Prod of Name.t * t * t
    | Cst of Name.t
  [@@deriving show]

  let mkVar name = Var name

  let mkApp f arg =
    match f with
    | App (f, f_args) -> App (f, f_args @ [ arg ])
    | _ -> App (f, [ arg ])

  let mkApps f args =
    assert (not @@ List.is_empty args);
    match f with App (f, f_args) -> App (f, f_args @ args) | _ -> App (f, args)

  let mkLambda name ty body = Lambda (name, ty, body)
  let mkArrow left right = Arrow (left, right)
  let mkProd name ty body = Prod (name, ty, body)
  let mkCst name = Cst name

  module Gen = struct
    open QCheck2

    let ( let* ) = Gen.bind

    let gen_name : Name.t Gen.t =
      Gen.(map Name.make @@ string_size ~gen:printable (1 -- 20))

    let split_nat n : (int * int) Gen.t =
      assert (n >= 0);
      let* k = Gen.(0 -- n) in
      Gen.return (k, n - k)

    (** Generate a term with exactly [n] nodes interior nodes 
        (i.e. not counting variables and constants). *)
    let rec simple_sized n : t Gen.t =
      let open Gen in
      if n <= 0
      then oneof [ mkVar <$> gen_name; mkCst <$> gen_name ]
      else
        let* n1, n2 = split_nat (n - 1) in
        oneof
          [ mkLambda <$> gen_name <*> simple_sized n1 <*> simple_sized n2
          ; mkProd <$> gen_name <*> simple_sized n1 <*> simple_sized n2
          ; mkArrow <$> simple_sized n1 <*> simple_sized n2
          ; mkApp <$> simple_sized n1 <*> simple_sized n2
          ]

    let simple : t Gen.t = Gen.sized simple_sized
  end
end

(***************************************************************************************)
(** Environments *)

module Env = struct
  type pp_info = { symbol : string; position : [ `Prefix | `Infix | `Suffix ] }
  [@@deriving show]

  type t = { constants : Term.t Name.Map.t; pp_info : pp_info Name.Map.t }

  let empty = { constants = Name.Map.empty; pp_info = Name.Map.empty }

  let add_constant name ty env =
    { env with constants = Name.Map.add name ty env.constants }
end
