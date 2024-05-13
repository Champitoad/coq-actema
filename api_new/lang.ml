(***************************************************************************************)
(** Names *)

module Name : sig
  type t [@@deriving show]

  val str : t -> string
  val make : string -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int

  module Map : Map.S with type key = t
end = struct
  type t = { str : string; tag : int } [@@deriving show]

  let str var = var.str

  (** This function uses some mutable state internally. *)
  let make =
    (* [max_tag[x]] stores the maximum tag that was used to create a variable with name [x]. *)
    let max_tag : (string, int) Hashtbl.t = Hashtbl.create 32 in
    fun str ->
      let tag =
        match Hashtbl.find_opt max_tag str with None -> 0 | Some n -> n + 1
      in
      Hashtbl.replace max_tag str tag;
      { str; tag }

  let equal v1 v2 = v1.tag = v2.tag
  let compare v1 v2 = compare v1.tag v2.tag

  module Map = Map.Make (struct
    type nonrec t = t

    let compare = compare
  end)
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

  let mkApp f arg =
    match f with
    | App (f, f_args) -> App (f, f_args @ [ arg ])
    | _ -> App (f, [ arg ])

  let mkApps f args =
    assert (not @@ List.is_empty args);
    match f with App (f, f_args) -> App (f, f_args @ args) | _ -> App (f, args)
end

(***************************************************************************************)
(** Environments *)

module Env = struct
  type pp_info = { symbol : string; position : [ `Prefix | `Infix | `Suffix ] }
  [@@deriving show]

  type t =
    { globals : Term.t Name.Map.t
    ; locals : Term.t Name.Map.t
    ; pp_info : pp_info Name.Map.t
    }

  let empty =
    { globals = Name.Map.empty
    ; locals = Name.Map.empty
    ; pp_info = Name.Map.empty
    }

  let union env1 env2 =
    let check_binding _key value1 value2 =
      assert (value1 = value2);
      Some value1
    in
    { globals = Name.Map.union check_binding env1.globals env2.globals
    ; locals = Name.Map.union check_binding env1.locals env2.locals
    ; pp_info = Name.Map.union check_binding env1.pp_info env2.pp_info
    }
end
