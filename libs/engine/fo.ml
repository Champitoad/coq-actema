(* -------------------------------------------------------------------- *)
open Utils
open Location
open Syntax

(* -------------------------------------------------------------------- *)
type name = string

type ty =
  | TUnit
  | TOr  of ty * ty
  | TAnd of ty * ty

type arity = ty list

(* -------------------------------------------------------------------- *)
let tunit = TUnit
let tor   = fun x y -> TOr  (x, y)
let tand  = fun x y -> TAnd (x, y)

(* -------------------------------------------------------------------- *)
type expr =
  | EVar of int
  | EGbl of name
  | EUnit
  | EOr  of [`Left | `Right] * ty * expr
  | EAnd of expr * expr
  | EOp  of name * expr list

type form =
  | FTrue
  | FFalse
  | FPred of name * expr list
  | FConn of logcon * form list
  | FBind of logbnd * (name * ty) * form

and logcon = [ `And | `Or | `Not ]
and logbnd = [ `Forall | `Exists ]

(* -------------------------------------------------------------------- *)
type env = {
  env_ops : (name, openv) Map.t;  
  env_pds : (name, pdenv) Map.t;
  env_vrs : (name, lcenv) Map.t;
  env_lcs : lcenv list;
}

and openv = {
  oe_name  : name;
  oe_type  : ty list;
  oe_resty : ty;
}

and pdenv = {
  pe_name : name;
  pe_type : ty list;
}

and lcenv = {
  le_name : name;
  le_ty   : ty;
}

(* -------------------------------------------------------------------- *)
exception DuplicatedEntry of [`Op | `Pred | `Var] * name

(* -------------------------------------------------------------------- *)
module Op : sig
  val push  : env -> openv -> env
  val push1 : env -> name -> arity * ty -> env
  val oget  : env -> name -> openv option
  val get   : env -> exn:exn -> name -> openv
end = struct
  let push (env : env) (op : openv) =
    match Map.add_carry op.oe_name op env.env_ops with
    | _, Some _ -> raise (DuplicatedEntry (`Op, op.oe_name))
    | env_ops, _ -> { env with env_ops }

  let push1 (env : env) (name : name) ((at, rt) : arity * ty) =
    let op = { oe_name = name; oe_type = at; oe_resty = rt; } in
    push env op

  let oget (env : env) (name : name) =
    Map.Exceptionless.find name env.env_ops

  let get (env : env) ~exn (name : name) =
    Option.get_exn (oget env name) exn
end

(* -------------------------------------------------------------------- *)
module Pred : sig
  val push  : env -> pdenv -> env
  val push1 : env -> name -> arity -> env
  val oget  : env -> name -> pdenv option
  val get   : env -> exn:exn -> name -> pdenv
end = struct
  let push (env : env) (pe : pdenv) =
    match Map.add_carry pe.pe_name pe env.env_pds with
    | _, Some _ -> raise (DuplicatedEntry (`Pred, pe.pe_name))
    | env_pds, _ -> { env with env_pds }

  let push1 (env : env) (name : name) (at : arity) =
    let pred = { pe_name = name; pe_type = at; } in
    push env pred

  let oget (env : env) (name : name) =
    Map.Exceptionless.find name env.env_pds

  let get (env : env) ~exn (name : name) =
    Option.get_exn (oget env name) exn 
end

(* -------------------------------------------------------------------- *)
module Vars : sig
  val push  : env -> name -> ty -> env
  val oget  : env -> name -> (name * ty) option
  val get   : env -> exn:exn -> name -> name * ty
  val getty : env -> exn:exn -> name -> ty
end = struct
  let push (env : env) (name : name) (ty : ty) =
    let var = { le_name = name; le_ty = ty; } in
    match Map.add_carry name var env.env_vrs with
    | _, Some _ -> raise (DuplicatedEntry (`Var, name))
    | env_vrs, _ -> { env with env_vrs }

  let oget (env : env) (name : name) =
    Map.Exceptionless.find name env.env_vrs />
      (fun lc -> (lc.le_name, lc.le_ty))

  let get (env : env) ~exn (name : name) =
    Option.get_exn (oget env name) exn 

  let getty (env : env) ~exn (name : name) =
    snd (get env ~exn name)
end

(* -------------------------------------------------------------------- *)
module Locals : sig
  val push  : env -> name -> ty -> env
  val oget  : env -> idx:int -> (name * ty) option
  val get   : env -> exn:exn -> idx:int -> name * ty
  val getty : env -> exn:exn -> idx:int -> ty  
end = struct
  let push (env : env) (name : name) (ty : ty) =
    let lc = { le_name = name; le_ty = ty; } in
    { env with env_lcs = lc :: env.env_lcs }

  let oget (env : env) ~(idx : int) =
    match List.Exceptionless.at env.env_lcs idx with
    | `Ok x -> Some (x.le_name, x.le_ty)
    | `Invalid_argument _ -> None

  let get (env : env) ~exn ~(idx : int) =
    Option.get_exn (oget env ~idx) exn

  let getty (env : env) ~exn ~(idx : int) =
    snd (get env ~exn ~idx)
end

(* -------------------------------------------------------------------- *)
module Ty : sig
  module Compatible : sig
    val type_ : ty -> ty -> bool
    val arity : arity -> arity -> bool
  end
end = struct
  module Compatible = struct
    let type_ (ty1 : ty) (ty2 : ty) =
      (ty1 ==(*phi*) ty2) || (ty1 = ty2)

    let arity (a1 : arity) (a2 : arity) =
      try  List.for_all2 type_ a1 a2
      with Invalid_argument _ -> false
  end
end

(* -------------------------------------------------------------------- *)
exception RecheckFailure

module Expr : sig
  val recheck : env -> expr -> ty
end = struct
  let recheck (env : env) =
    let rec recheck (e : expr) : ty =
      match e with
      | EVar i ->
          Locals.getty env ~exn:RecheckFailure ~idx:i
      | EGbl name ->
          Vars.getty env ~exn:RecheckFailure name
      | EUnit ->
          tunit
      | EOp (op, args) ->
          let op   = Op.get env ~exn:RecheckFailure op in
          let args = List.map recheck args in
          if not (Ty.Compatible.arity args op.oe_type) then
            raise RecheckFailure;
          op.oe_resty
      | EOr (side, infty, e) -> begin
          let ety = recheck e in
          match side with
          | `Left  -> tor ety infty
          | `Right -> tor infty ety
        end
      | EAnd (e1, e2) ->
          let ty1 = recheck e1 in
          let ty2 = recheck e2 in
          tand ty1 ty2

    in fun (e : expr) -> recheck e
end

(* -------------------------------------------------------------------- *)
module Form : sig
  val parity  : logcon -> int
  val check   : pform -> form
  val recheck : env -> form -> unit
  val mathml  : form -> Tyxml.Xml.elt
end = struct
  let parity (lg : logcon) =
    match lg with
    | `And -> 2 | `Or  -> 2 | `Not -> 1

  let rec recheck (env : env) (form : form) : unit =
    match form with
    | FTrue | FFalse -> ()
    | FPred (pred, args) ->
        let pred = Pred.get env ~exn:RecheckFailure pred in
        let args = List.map (Expr.recheck env) args in
        if not (Ty.Compatible.arity args pred.pe_type) then
          raise RecheckFailure
    | FConn (lg, forms) ->
        List.iter (recheck env) forms;
        if List.length forms <> parity lg then
          raise RecheckFailure

    | FBind (_bnd, (name, ty), body) ->
        let env = Locals.push env name ty in
        recheck env body

  let check (form : pform) =
    match unloc form with
    | PFCst true  -> FTrue
    | PFCst false -> FFalse

    | _ -> assert false

  let mathml =
    let open Tyxml in

    let _mo c = Xml.node "mo" [c] in
    let  mi c = Xml.node "mi" [c] in

    let rec aux (form : form) =
      match form with
      | FTrue ->
          mi (Xml.entity "#x22A5")
      | FFalse ->
          mi (Xml.entity "#x22A4")
      | _ ->
          mi (Xml.entity "?")

    in fun (form : form) ->
      Xml.node "math" [aux form]
end
