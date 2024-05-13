(***************************************************************************************)
(** Names *)

module Name : sig
  type t

  val str : t -> string
  val make : string -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int

  module Map : Map.S with type key = t
end = struct
  type t = { str : string; tag : int }

  let str var = var.str

  (** This function uses some mutable state internally. *)
  let make =
    (* [max_tag[x]] stores the maximum tag that was used to create a variable with name [x]. *)
    let max_tag : (string, int) Hashtbl.t = Hashtbl.create 32 in
    fun str ->
      let tag = match Hashtbl.find_opt max_tag str with None -> 0 | Some n -> n + 1 in
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
end

(***************************************************************************************)
(** Environments *)

module Env = struct
  type pp_info = { symbol : string; position : [ `Prefix | `Infix | `Suffix ] }
  type t = { globals : Term.t Name.Map.t; locals : Term.t Name.Map.t; pp : pp_info Name.Map.t }
end
