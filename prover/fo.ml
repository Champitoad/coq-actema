(* -------------------------------------------------------------------- *)
open Utils
open Location
open Syntax

(* -------------------------------------------------------------------- *)
(** Names *)

type name = string
type vname = name * int

let name_of_vname : vname -> name = fst

module Name = struct
  type t = name

  let equal = String.equal
  let compare = String.compare
  let hash = Hashtbl.hash
end

(* ------------------------------------------------------------------- *)
(** Handles *)

module Handle : sig
  include Map.OrderedType

  val ofint : int -> t
  val fresh : unit -> t
  val eq : t -> t -> bool
  val toint : t -> int
end = struct
  type t = int

  let compare = Utils.Uid.compare
  let fresh () : t = Utils.Uid.fresh ()
  let ofint (i : int) : t = i
  let toint (t : t) : int = t
  let eq = (( = ) : t -> t -> bool)
end

module Hidmap = struct
  open Api
  module HandleMap = Map.Make (Handle)

  type hidmap = Logic.uid HandleMap.t

  module Env = struct
    type t = hidmap
  end

  module State = Monad.State (Env)
  open State

  let empty = HandleMap.empty

  let find (hd : Handle.t) : Logic.uid State.t =
    let* hm = get in
    return (HandleMap.find hd hm)

  let push (id : Logic.uid) : Handle.t State.t =
    let hd = Handle.fresh () in
    let* hm = get in
    let* _ = put (HandleMap.add hd id hm) in
    return hd

  let union (m1 : hidmap) (m2 : hidmap) : hidmap =
    let f _ x _ = Some x in
    HandleMap.union f m1 m2

  let to_string m =
    m |> HandleMap.bindings
    |> List.to_string (fun (hd, id) -> Printf.sprintf "%d -> %s" (Handle.toint hd) id)
end

(* -------------------------------------------------------------------- *)
(* Types *)

type type_ =
  | TVar of vname
  | TUnit
  | TProd of type_ * type_
  | TOr of type_ * type_
  | TRec of name * type_

type arity = type_ list
and sig_ = arity * type_

(* -------------------------------------------------------------------- *)
(** Expressions *)

type expr = EVar of vname | EFun of name * expr list

let rec e_vars =
  let open Monad.List in
  function EVar x -> return x | EFun (_, ts) -> ts >>= e_vars

let rec e_vars =
  let open Monad.List in
  function EVar x -> return x | EFun (_, ts) -> ts >>= e_vars

(* -------------------------------------------------------------------- *)
(* Formulas *)

type logcon = [ `And | `Or | `Imp | `Equiv | `Not ]
type bkind = [ `Forall | `Exist ]

type form =
  | FTrue
  | FFalse
  | FPred of name * expr list
  | FConn of logcon * form list
  | FBind of bkind * name * type_ * form

(* -------------------------------------------------------------------- *)
(* Terms = Formulas + Expressions *)

type term = [ `F of form | `E of expr ]

let term_of_expr e : term = `E e
let term_of_form f : term = `F f

let expr_of_term (t : term) =
  match t with `E e -> e | _ -> raise (Invalid_argument "Expected an expression")

let form_of_term (t : term) =
  match t with `F f -> f | _ -> raise (Invalid_argument "Expected a formula")

(* -------------------------------------------------------------------- *)
(* Contexts *)

(* Immediate Formula ConTeXt *)
type ifctx = CConn of logcon * form list * int | CBind of bkind * name * type_

(* Immediate Expression ConTexT *)
type iectx = CFun of name * expr list * int

(* Immediate term ConTexT *)
type ictx = [ `F of ifctx | `P of name * expr list * int | `E of iectx | `None ]

(* Uniform contexts are just lists *)
type fctx = ifctx list
type ectx = iectx list

(* A subterm is either a subformula, a subexpression in isolation,
   or a subexpression occurring in a predicate argument *)
type ctx = CForm of fctx | CExpr of ectx | CExprPred of fctx * name * expr list * int * ectx

(* -------------------------------------------------------------------- *)
(* Unification *)

type sitem = Sbound of expr | Sflex
type 'a eqns = ('a * 'a) list

(* -------------------------------------------------------------------- *)
(* Environments *)

type env =
  { env_prp : (name, arity) Map.t
  ; env_fun : (name, sig_) Map.t
  ; env_prp_name : (name, name) Map.t
  ; env_fun_name : (name, name) Map.t
  ; env_sort_name : (name, name) Map.t
  ; env_tvar : (name, type_ option list) Map.t
  ; env_var : (name, bvar list) Map.t
  ; env_evar : (name, type_ list) Map.t
  ; env_handles : (vname, Handle.t) BiMap.t
  }

and bvar = type_ * expr option

(* -------------------------------------------------------------------- *)
module Env : sig
  val nat : type_
  val zero : expr
  val succ : expr -> expr
  val add : expr -> expr -> expr
  val mult : expr -> expr -> expr

  (** An environment that contains only the basic arithmetic constants (add, mult, etc.). *)
  val empty : env

  (** The union of two environments. *)
  val union : env -> env -> env

  (** Given an environment [env] and a formula [f], filter [env] by keeping only the symbols needed to type [f]. *)
  val restrict_to_form : env -> form -> env
end = struct
  let nat = TVar ("nat", 0)
  let zero = EFun ("Z", [])
  let succ n = EFun ("S", [ n ])
  let add n m = EFun ("add", [ n; m ])
  let mult n m = EFun ("mult", [ n; m ])

  let empty : env =
    Map.
      { env_prp = empty
      ; env_fun =
          empty
          |> add "Z" ([], nat)
          |> add "S" ([ nat ], nat)
          |> add "add" ([ nat; nat ], nat)
          |> add "mult" ([ nat; nat ], nat)
      ; env_prp_name = empty
      ; env_fun_name = empty
      ; env_sort_name = empty
      ; env_var = empty
      ; env_tvar = empty |> add "nat" [ None ]
      ; env_evar = empty
      ; env_handles = BiMap.empty
      }

  let union a b =
    { env_prp = Map.union a.env_prp b.env_prp
    ; env_fun = Map.union a.env_fun b.env_fun
    ; env_prp_name = Map.union a.env_prp_name b.env_prp_name
    ; env_fun_name = Map.union a.env_fun_name b.env_fun_name
    ; env_sort_name = Map.union a.env_sort_name b.env_sort_name
    ; env_var = Map.union a.env_var b.env_var
    ; env_tvar = Map.union a.env_tvar b.env_tvar
    ; env_evar = Map.union a.env_evar b.env_evar
    ; env_handles = BiMap.union a.env_handles b.env_handles
    }

  let rec collect_form_symbols env f acc : env =
    match f with
    | FTrue | FFalse -> acc
    | FPred (pname, exps) ->
        (* Recurse on the children. *)
        let acc =
          List.fold
            begin
              fun acc e -> collect_exp_symbols env e acc
            end
            acc exps
        in
        (* Collect the predicate symbol. *)
        if not (Map.mem pname acc.env_prp)
        then
          let ar = Map.find pname acc.env_prp in
          let pname' = Map.find pname acc.env_prp_name in
          { acc with
            env_prp = Map.add pname ar acc.env_prp
          ; env_prp_name = Map.add pname pname' acc.env_prp_name
          }
        else acc
    | FConn (_, forms) ->
        (* Simply recurse on the children. *)
        List.fold
          begin
            fun acc f -> collect_form_symbols env f acc
          end
          acc forms
    | FBind (_, _, ty, f) ->
        (* Collect the type. *)
        let acc = collect_type_symbols env ty acc in
        (* Recurse on the child. *)
        collect_form_symbols env f acc

  and collect_exp_symbols env e acc : env =
    match e with
    | EVar _ -> (* Nothing to do. *) acc
    | EFun (fname, exps) ->
        (* Recurse on the children. *)
        let acc =
          List.fold
            begin
              fun acc e -> collect_exp_symbols env e acc
            end
            acc exps
        in
        (* Collect the function symbol. *)
        if not (Map.mem fname acc.env_fun)
        then
          let sig_ = Map.find fname env.env_fun in
          let fname' = Map.find fname env.env_fun_name in
          { acc with
            env_fun = Map.add fname sig_ acc.env_fun
          ; env_fun_name = Map.add fname fname' acc.env_fun_name
          }
        else acc

  and collect_type_symbols env t acc : env =
    match t with
    | TUnit -> acc
    | TOr (t1, t2) | TProd (t1, t2) ->
        let acc = collect_type_symbols env t1 acc in
        collect_type_symbols env t2 acc
    | _ -> acc

  let restrict_to_form env f = collect_form_symbols env f empty
end

(* -------------------------------------------------------------------- *)
exception DuplicatedEntry of [ `Prp | `Fun ] * name

(* -------------------------------------------------------------------- *)
module LEnv : sig
  type lenv

  exception EmptyLEnv

  val empty : lenv
  val indices : lenv -> (name, int) Map.t
  val bindings : lenv -> (name * type_) list
  val get_index : lenv -> name -> int
  val exists : lenv -> vname -> bool
  val enter : lenv -> name -> type_ -> lenv
  val exit : lenv -> lenv
  val fold : lenv -> name -> type_ -> 'a -> (lenv -> 'a -> 'b) -> 'b
end = struct
  type lenv = { le_indices : (name, type_ list) Map.t; le_bindings : (name * type_) list }

  exception EmptyLEnv

  let empty = { le_indices = Map.empty; le_bindings = [] }
  let indices lenv = Map.map (List.length |>> ( - ) 1) lenv.le_indices
  let bindings lenv = lenv.le_bindings
  let get_index (lenv : lenv) (name : name) = Map.find name (indices lenv)
  let exists (lenv : lenv) (x : vname) = List.mem x (Map.bindings (indices lenv))

  let enter (lenv : lenv) (name : name) (ty : type_) =
    { le_indices = Map.modify_def [] name (List.cons ty) lenv.le_indices
    ; le_bindings = (name, ty) :: lenv.le_bindings
    }

  let exit (lenv : lenv) =
    match lenv.le_bindings with
    | [] -> raise EmptyLEnv
    | (name, _) :: bds ->
        let update bds =
          let bds = Option.get bds |> List.tl in
          if bds = [] then None else Some bds
        in

        { le_bindings = bds; le_indices = Map.modify_opt name update lenv.le_indices }

  let fold (lenv : lenv) (name : name) (ty : type_) (x : 'a) (f : lenv -> 'a -> 'b) =
    f (enter lenv name ty) x
end

(* -------------------------------------------------------------------- *)
module Prps : sig
  val push : env -> name * arity -> env
  val exists : env -> name -> bool
  val get : env -> name -> arity option
  val all : env -> (name, arity) Map.t
end = struct
  let push (env : env) ((name, sg) : name * arity) =
    if Map.mem name env.env_prp then raise (DuplicatedEntry (`Prp, name));
    { env with env_prp = Map.add name sg env.env_prp }

  let get (env : env) (name : name) = Map.Exceptionless.find name env.env_prp
  let exists (env : env) (name : name) = Option.is_some (get env name)
  let all (env : env) = env.env_prp
end

(* -------------------------------------------------------------------- *)
module Funs : sig
  val push : env -> name * sig_ -> env
  val exists : env -> name -> bool
  val get : env -> name -> sig_ option
  val all : env -> (name, sig_) Map.t
end = struct
  let push (env : env) ((name, sg) : name * sig_) =
    if Map.mem name env.env_prp then raise (DuplicatedEntry (`Fun, name));
    { env with env_fun = Map.add name sg env.env_fun }

  let get (env : env) (name : name) = Map.Exceptionless.find name env.env_fun
  let exists (env : env) (name : name) = Option.is_some (get env name)
  let all (env : env) = env.env_fun
end

(* -------------------------------------------------------------------- *)
module TVars : sig
  val push : env -> name * type_ option -> env
  val get : env -> vname -> type_ option option
  val exists : env -> vname -> bool
  val all : env -> (name, type_ option list) Map.t
end = struct
  let push (env : env) ((name, body) : name * type_ option) =
    { env with
      env_tvar =
        Map.modify_opt name
          (fun bds ->
            let v = body :: Option.default [] bds in
            Some v)
          env.env_tvar
    }

  let get (env : env) ((name, idx) : vname) =
    let bds = Map.find_default [] name env.env_tvar in
    List.nth_opt bds idx

  let exists (env : env) (x : vname) = get env x |> Option.is_some
  let all (env : env) = env.env_tvar
end

(* -------------------------------------------------------------------- *)
(* Notations *)

module Notation : sig
  open Tyxml

  val t_toascii : env -> type_ -> string
  val t_tostring : env -> type_ -> string
  val t_tohtml : env -> type_ -> Xml.elt
  val t_tomathml : env -> type_ -> Xml.elt
  val e_toascii : env -> expr -> string
  val e_tostring : env -> expr -> string
  val e_tohtml : ?id:string option -> env -> expr -> Xml.elt
  val e_tomathml : ?id:string option -> env -> expr -> Xml.elt
  val f_toascii : env -> form -> string
  val f_tostring : env -> form -> string
  val f_tohtml : ?id:string option -> env -> form -> Xml.elt
  val f_tomathml : ?id:string option -> env -> form -> Xml.elt
  val toascii : env -> term -> string
  val tostring : env -> term -> string
  val tohtml : ?id:string option -> env -> term -> Xml.elt
  val tomathml : ?id:string option -> env -> term -> Xml.elt
end = struct
  open Tyxml

  let rec prio_of_form = function
    | FTrue -> max_int
    | FFalse -> max_int
    | FPred _ -> max_int
    | FConn (op, _) -> prio_of_op op
    | FBind _ -> min_int

  and prio_of_expr = function EVar _ -> max_int | EFun (f, _) -> prio_of_fun f

  and prio_of_type = function
    | TUnit -> max_int
    | TVar _ -> max_int
    | TProd _ -> prio_And
    | TOr _ -> prio_Or
    | TRec _ -> min_int

  and prio_of_op = function
    | `Not -> prio_Not
    | `And -> prio_And
    | `Or -> prio_Or
    | `Imp -> prio_Imp
    | `Equiv -> prio_Equiv

  and prio_of_fun = function "Z" -> max_int | "S" -> 3 | "mult" -> 2 | "add" -> 1 | _ -> min_int
  and prio_Not = 5
  and prio_And = 4
  and prio_Or = 3
  and prio_Imp = 2
  and prio_Equiv = 1

  let left_assoc = [ ( < ); ( <= ) ]
  let right_assoc = [ ( <= ); ( < ) ]
  let no_assoc = [ ( <= ); ( <= ) ]

  let assoc_of_op = function
    | `Not -> [ ( < ) ]
    | `And | `Or -> left_assoc
    | `Imp -> right_assoc
    | `Equiv -> no_assoc

  let assoc_of_fun = function
    | "Z" -> []
    | "S" -> [ ( < ) ]
    | "add" | "mult" -> left_assoc
    | _ -> assert false

  let unicode_of_op = function
    | `Not -> 0x00AC
    | `And -> 0x2227
    | `Or -> 0x2228
    | `Imp -> 0x27F9
    | `Equiv -> 0x27FA

  let ascii_of_op = function
    | `Not -> "~"
    | `And -> "&&"
    | `Or -> "||"
    | `Imp -> "->"
    | `Equiv -> "<->"

  let shortname x m = try Map.find x m with Not_found -> x

  let f_toascii, e_toascii, t_toascii =
    let open Text in
    let rec for_type ?(is_pr = false) env =
      pr ~doit:is_pr <<| function
      | TUnit -> "()"
      | TVar (x, 0) -> shortname x env.env_sort_name
      | TVar (x, i) -> Printf.sprintf "%s{%d}" x i
      | (TProd (t1, t2) | TOr (t1, t2)) as ty ->
          let t1 = for_type env ~is_pr:(prio_of_type t1 < prio_of_type ty) t1 in
          let t2 = for_type env ~is_pr:(prio_of_type t2 <= prio_of_type ty) t2 in
          let tycon =
            begin
              match ty with TProd _ -> '*' | TOr _ -> '+' | _ -> assert false
            end
          in
          t1 ^ spaced (UTF8.of_char (UChar.of_char tycon)) ^ t2
      | TRec (x, t) -> Format.sprintf "rec %s . %s" x (for_type env t)
    and for_expr env = function
      | EVar (x, 0) -> x
      | EVar (x, i) -> Format.sprintf "%s{%d}" x i
      | EFun (f, args) ->
          let args = String.concat ", " (List.map (for_expr env) args) in
          shortname f env.env_fun_name ^ pr args
    and for_form ?(is_pr = false) env =
      pr ~doit:is_pr <<| function
      | FTrue -> "true"
      | FFalse -> "false"
      | FConn (lg, fs) -> begin
          let text_lg = lg |> ascii_of_op in
          let text_fs =
            List.combine fs (assoc_of_op lg)
            |> List.map (fun (f, cmp) ->
                   for_form env ~is_pr:(cmp (prio_of_form f) (prio_of_op lg)) f)
          in

          match (lg, text_fs) with
          | (`And | `Or | `Imp | `Equiv), [ f1; f2 ] -> f1 ^ spaced text_lg ^ f2
          | `Not, [ f ] -> spaced ~left:false text_lg ^ f
          | (`And | `Or | `Imp | `Not | `Equiv), _ -> assert false
        end
      | FPred ("_EQ", [ e1; e2 ]) -> Format.sprintf "%s = %s" (for_expr env e1) (for_expr env e2)
      | FPred (name, []) -> shortname name env.env_prp_name
      | FPred (name, args) ->
          let args = List.map (for_expr env) args in
          let args = String.join ", " args in
          shortname name env.env_prp_name ^ pr args
      | FBind (bd, x, ty, f) ->
          let bd = match bd with `Forall -> "forall" | `Exist -> "exists" in
          Format.sprintf "%s %s : %s . %s" bd x (for_type env ty) (for_form env f)
    in

    ((fun f -> for_form f), (fun e -> for_expr e), fun t -> for_type t)

  let toascii env = function `E e -> e_toascii env e | `F f -> f_toascii env f

  let f_tostring, e_tostring, t_tostring =
    let open Text in
    let rec for_type ?(is_pr = false) env =
      pr ~doit:is_pr <<| function
      | TUnit -> "()"
      | TVar ("nat", _) -> "ℕ"
      | TVar (x, 0) -> shortname x env.env_sort_name
      | TVar (x, i) -> Printf.sprintf "%s{%d}" x i
      | (TProd (t1, t2) | TOr (t1, t2)) as ty ->
          let t1 = for_type env ~is_pr:(prio_of_type t1 < prio_of_type ty) t1 in
          let t2 = for_type env ~is_pr:(prio_of_type t2 <= prio_of_type ty) t2 in
          let tycon =
            begin
              match ty with TProd _ -> '*' | TOr _ -> '+' | _ -> assert false
            end
          in
          t1 ^ spaced (UTF8.of_char (UChar.of_char tycon)) ^ t2
      | TRec (x, t) -> Format.sprintf "rec %s . %s" x (for_type env t)
    and for_expr ?(_is_pr = false) env expr =
      match expr with
      | EVar (x, 0) -> x
      | EVar (x, i) -> Format.sprintf "%s{%d}" x i
      | EFun ("_dummy", _) -> "😬"
      | EFun (("Z" as f), es)
      | EFun (("S" as f), es)
      | EFun (("add" as f), es)
      | EFun (("mult" as f), es) ->
          let str es =
            List.combine es (assoc_of_fun f)
            |> List.mapi (fun _ (e, cmp) ->
                   for_expr env ~_is_pr:(cmp (prio_of_expr e) (prio_of_fun f)) e)
          in

          begin
            match (f, str es) with
            | "Z", [] -> "0"
            | "S", _ ->
                let rec numeral num = function
                  | EFun ("S", [ x ]) -> numeral (num + 1) x
                  | EFun ("Z", []) -> string_of_int num
                  | e -> (str [ e ] |> List.hd) ^ "⊕" ^ string_of_int num
                in
                numeral 0 expr
            | "add", [ e1; e2 ] -> e1 ^ spaced "+" ^ e2
            | "mult", [ e1; e2 ] -> e1 ^ spaced "⋅" ^ e2
            | _ -> assert false
          end
      | EFun (f, args) ->
          let args = String.concat ", " (List.map (for_expr env) args) in
          shortname f env.env_fun_name ^ pr args
    and for_form ?(is_pr = false) env =
      pr ~doit:is_pr <<| function
      | FTrue -> UTF8.of_char (UChar.chr 0x22A4)
      | FFalse -> UTF8.of_char (UChar.chr 0x22A5)
      | FConn (`Not, [ FPred ("_EQ", [ e1; e2 ]) ]) ->
          for_expr env e1 ^ spaced (UTF8.of_char (UChar.chr 0x2260)) ^ for_expr env e2
      | FConn (lg, fs) -> begin
          let text_lg = lg |> unicode_of_op |> UChar.chr |> UTF8.of_char in
          let text_fs =
            List.combine fs (assoc_of_op lg)
            |> List.map (fun (f, cmp) ->
                   for_form env ~is_pr:(cmp (prio_of_form f) (prio_of_op lg)) f)
          in

          match (lg, text_fs) with
          | (`And | `Or | `Imp | `Equiv), [ f1; f2 ] -> f1 ^ spaced text_lg ^ f2
          | `Not, [ f ] -> spaced ~left:false text_lg ^ f
          | (`And | `Or | `Imp | `Not | `Equiv), _ -> assert false
        end
      | FPred ("_dummy", _) -> "🫠"
      | FPred ("_EQ", [ e1; e2 ]) -> Format.sprintf "%s = %s" (for_expr env e1) (for_expr env e2)
      | FPred (name, []) -> shortname name env.env_prp_name
      | FPred (name, args) ->
          let args = List.map (for_expr env) args in
          let args = String.join ", " args in
          shortname name env.env_prp_name ^ pr args
      | FBind (bd, x, ty, f) ->
          let bd =
            match bd with
            | `Forall -> UTF8.of_char (UChar.chr 0x2200)
            | `Exist -> UTF8.of_char (UChar.chr 0x2203)
          in
          Format.sprintf "%s%s : %s . %s" bd x (for_type env ty) (for_form env f)
    in

    ((fun f -> for_form f), (fun e -> for_expr e), fun t -> for_type t)

  let tostring env = function `E e -> e_tostring env e | `F f -> f_tostring env f

  let f_tohtml, e_tohtml, t_tohtml =
    let open Utils.Html in
    let rec for_type ?(is_pr = false) env (ty : type_) =
      let data =
        match ty with
        | TUnit -> [ span [ Xml.pcdata "()" ] ]
        | TVar ("nat", _) -> [ span [ Xml.pcdata "ℕ" ] ]
        | TVar (x, 0) -> [ span [ Xml.pcdata (shortname x env.env_sort_name) ] ]
        | TVar (x, i) -> [ span [ Xml.pcdata (Printf.sprintf "%s{%d}" x i) ] ]
        | TProd (t1, t2) | TOr (t1, t2) ->
            let t1 = for_type env ~is_pr:(prio_of_type t1 < prio_of_type ty) t1 in
            let t2 = for_type env ~is_pr:(prio_of_type t2 <= prio_of_type ty) t2 in
            let tycon = match ty with TProd _ -> '*' | TOr _ -> '+' | _ -> assert false in
            t1 @ spaced [ Xml.pcdata (UTF8.of_char (UChar.of_char tycon)) ] @ t2
        | TRec (x, t) ->
            let aout =
              [ [ span [ Xml.pcdata "rec" ] ] ]
              @ [ [ span [ Xml.pcdata x ] ] ]
              @ [ [ span [ Xml.pcdata "." ] ] ]
              @ [ [ span (for_type env t) ] ]
            in
            List.flatten (List.join [ span [ Xml.entity "nbsp" ] ] aout)
      in

      [ span (pr ~doit:is_pr data) ]
    and for_expr ?(id : string option option) ?(is_pr = false) env (p : int list) (expr : expr) :
        Xml.elt list =
      let for_expr = for_expr ?id in

      let thisid p =
        id
        |> Option.map (fun prefix ->
               let p = String.concat "/" (List.rev_map string_of_int p) in
               Option.fold (fun p prefix -> Format.sprintf "%s:%s" prefix p) p prefix)
        |> Option.map (fun x -> Xml.string_attrib "id" x)
        |> List.of_option
      in

      let id = ref true in

      let data =
        match expr with
        | EVar (x, 0) -> [ span [ Xml.pcdata x ] ]
        | EVar (x, i) -> [ span [ Xml.pcdata (Printf.sprintf "%s{%d}" x i) ] ]
        | EFun ("_dummy", _) -> [ span [ Xml.pcdata "😬" ] ]
        | EFun (("Z" as f), es)
        | EFun (("S" as f), es)
        | EFun (("add" as f), es)
        | EFun (("mult" as f), es) ->
            let xml es p =
              List.combine es (assoc_of_fun f)
              |> List.mapi (fun i (e, cmp) ->
                     for_expr env ~is_pr:(cmp (prio_of_expr e) (prio_of_fun f)) (i :: p) e)
            in

            begin
              match (f, xml es p) with
              | "Z", [] -> [ span [ Xml.pcdata "0" ] ]
              | "S", _ ->
                  id := false;
                  let rec numeral acc num sub = function
                    | EFun ("S", [ x ]) ->
                        numeral (fun x -> [ span ~a:(thisid sub) (acc x) ]) (num + 1) (0 :: sub) x
                    | EFun ("Z", []) ->
                        [ span ~a:(thisid sub) (acc [ Xml.pcdata (string_of_int num) ]) ]
                    | e ->
                        acc
                          begin
                            (xml [ e ] (List.tl sub) |> List.hd)
                            @ [ span [ Xml.pcdata "⊕" ] ]
                            @ [ Xml.pcdata (string_of_int num) ]
                          end
                  in
                  numeral identity 0 p expr
              | "add", [ e1; e2 ] -> e1 @ spaced [ span [ Xml.pcdata "+" ] ] @ e2
              | "mult", [ e1; e2 ] -> e1 @ spaced [ span [ Xml.pcdata "⋅" ] ] @ e2
              | _ -> assert false
            end
        | EFun (name, args) ->
            let args = List.mapi (fun i e -> for_expr env (i :: p) e) args in
            let aout =
              [ [ span [ Xml.pcdata (shortname name env.env_fun_name) ] ] ]
              @ [ pr (List.flatten (List.join [ span [ Xml.pcdata ","; Xml.entity "nbsp" ] ] args))
                ]
            in

            List.flatten (List.join [ span [ Xml.entity "nbsp" ] ] aout)
      in

      [ span ~a:(if !id then thisid p else []) (pr ~doit:is_pr data) ]
    and for_form ?(id : string option option) ?(is_pr = false) env (p : int list) (form : form) =
      let for_form = for_form ?id in

      let thisid p =
        id
        |> Option.map (fun prefix ->
               let p = String.concat "/" (List.rev_map string_of_int p) in
               Option.fold (fun p prefix -> Format.sprintf "%s:%s" prefix p) p prefix)
        |> Option.map (fun x -> Xml.string_attrib "id" x)
        |> List.of_option
      in

      let data =
        match form with
        | FTrue -> [ span [ Xml.entity "#x22A4" ] ]
        | FFalse -> [ span [ Xml.entity "#x22A5" ] ]
        | FConn (`Not, [ FPred ("_EQ", [ e1; e2 ]) ]) ->
            [ span
                ~a:(thisid (0 :: p))
                [ span (for_expr ?id env (0 :: 0 :: p) e1)
                ; span [ Xml.entity "nbsp"; Xml.entity "#x2260"; Xml.entity "nbsp" ]
                ; span (for_expr ?id env (1 :: 0 :: p) e2)
                ]
            ]
        | FConn (lg, fs) -> begin
            let xml_lg =
              let hexcode = Printf.sprintf "#x%x" (unicode_of_op lg) in
              [ span [ Xml.entity hexcode ] ]
            in

            let xml_fs =
              List.combine fs (assoc_of_op lg)
              |> List.mapi (fun i (f, cmp) ->
                     for_form env ~is_pr:(cmp (prio_of_form f) (prio_of_op lg)) (i :: p) f)
            in

            match (lg, xml_fs) with
            | (`And | `Or | `Imp | `Equiv), [ f1; f2 ] -> f1 @ spaced xml_lg @ f2
            | `Not, [ f ] -> spaced ~left:false xml_lg @ f
            | (`And | `Or | `Imp | `Not | `Equiv), _ -> assert false
          end
        | FPred ("_dummy", _) -> [ span [ Xml.pcdata "🫠" ] ]
        | FPred ("_EQ", [ e1; e2 ]) ->
            [ span (for_expr ?id env (0 :: p) e1)
            ; span [ Xml.entity "nbsp"; Xml.pcdata "="; Xml.entity "nbsp" ]
            ; span (for_expr ?id env (1 :: p) e2)
            ]
        | FPred (name, []) -> [ span [ Xml.pcdata (shortname name env.env_prp_name) ] ]
        | FPred (name, args) ->
            let args = List.mapi (fun i e -> for_expr ?id env (i :: p) e) args in
            let aout =
              [ [ span [ Xml.pcdata (shortname name env.env_prp_name) ] ] ]
              @ [ pr (List.flatten (List.join [ span [ Xml.pcdata ","; Xml.entity "nbsp" ] ] args))
                ]
            in

            List.flatten (List.join [ span [ Xml.entity "nbsp" ] ] aout)
        | FBind (bd, x, ty, f) ->
            let bd =
              match bd with
              | `Forall -> UTF8.of_char (UChar.chr 0x2200)
              | `Exist -> UTF8.of_char (UChar.chr 0x2203)
            in

            let aout =
              [ [ span [ Xml.pcdata bd ] ] ]
              @ [ [ span [ Xml.pcdata x ] ] ]
              @ [ [ span [ Xml.pcdata ":" ] ] ]
              @ [ [ span (for_type env ty) ] ]
              @ [ [ span [ Xml.pcdata "." ] ] ]
              @ [ for_form env (0 :: p) f ]
            in

            List.flatten (List.join [ span [ Xml.entity "nbsp" ] ] aout)
      in

      [ span ~a:(thisid p) (pr ~doit:is_pr data) ]
    in

    ( (fun ?id env (form : form) -> span (for_form ?id env [] form))
    , (fun ?id env (expr : expr) -> span (for_expr ?id env [] expr))
    , fun env (ty : type_) -> span (for_type env ty) )

  let tohtml ?id env = function `E e -> e_tohtml ?id env e | `F f -> f_tohtml ?id env f

  let f_tomathml, e_tomathml, t_tomathml =
    let open Tyxml in
    let open Utils.Mathml in
    let rec for_type ?(is_pr = false) env (ty : type_) =
      let data =
        match ty with
        | TUnit -> [ mo (UTF8.of_char (UChar.of_int 0x2022)) ]
        | TVar ("nat", _) -> [ mo "ℕ" ]
        | TVar (x, 0) -> [ mi (shortname x env.env_sort_name) ]
        | TVar (x, i) ->
            let x = Printf.sprintf "%s{%d}" x i in
            [ mi x ]
        | TProd (t1, t2) | TOr (t1, t2) ->
            let t1 = for_type env ~is_pr:(prio_of_type t1 < prio_of_type ty) t1 in
            let t2 = for_type env ~is_pr:(prio_of_type t2 <= prio_of_type ty) t2 in
            let tycon =
              match ty with
              | TProd _ -> UChar.of_int 0x00D7
              | TOr _ -> UChar.of_int 0x002B
              | _ -> assert false
            in
            t1 @ [ mo (UTF8.of_char tycon) ] @ t2
        | TRec (x, t) -> [ mo (UTF8.of_char (UChar.of_int 0x03BC)); mi x; mo "." ] @ for_type env t
      in

      [ pr ~doit:is_pr (row data) ]
    and for_expr ?(id : string option option) ?(is_pr = false) env (p : int list) (expr : expr) =
      let for_expr = for_expr ?id in

      let data =
        match expr with
        | EVar (x, 0) -> [ mi x ]
        | EVar (x, i) ->
            let x = Printf.sprintf "%s{%d}" x i in
            [ mi x ]
        | EFun (("Z" as f), es)
        | EFun (("S" as f), es)
        | EFun (("add" as f), es)
        | EFun (("mult" as f), es) ->
            let xml es p =
              List.combine es (assoc_of_fun f)
              |> List.mapi (fun i (e, cmp) ->
                     for_expr ~is_pr:(cmp (prio_of_expr e) (prio_of_fun f)) env (i :: p) e)
            in

            begin
              match (f, xml es p) with
              | "Z", [] -> [ mn "0" ]
              | "S", _ -> begin
                  match es with
                  | [ n ] ->
                      let rec numeral acc = function
                        | EFun ("S", [ x ]) -> numeral (acc + 1) x
                        | EFun ("Z", []) -> [ mn (string_of_int acc) ]
                        | e ->
                            (xml [ e ] (List.init (acc - 1) (fun _ -> 0) @ p) |> List.hd)
                            @ [ mo "⊕" ]
                            @ [ mn (string_of_int acc) ]
                      in
                      numeral 1 n
                  | _ -> assert false
                end
              | "add", [ e1; e2 ] -> e1 @ [ mo "+" ] @ e2
              | "mult", [ e1; e2 ] -> e1 @ [ mo "×" ] @ e2
              | _ -> assert false
            end
        | EFun (name, args) ->
            let args = List.mapi (fun i e -> for_expr env (i :: p) e) args in
            [ mi (shortname name env.env_fun_name) ]
            @ [ pr (row (List.flatten (List.join [ mo "," ] args))) ]
      in

      let thisid =
        id
        |> Option.map (fun prefix ->
               let p = String.concat "/" (List.rev_map string_of_int p) in
               Option.fold (fun p prefix -> Format.sprintf "%s:%s" prefix p) p prefix)
      in
      let thisid = thisid |> Option.map (Xml.string_attrib "id") in

      [ pr ~doit:is_pr (row ~a:(List.of_option thisid) data) ]
    and for_form ?(id : string option option) ?(is_pr = false) env (p : int list) (form : form) =
      let for_form = for_form ?id in

      let thisid p =
        id
        |> Option.map (fun prefix ->
               let p = String.concat "/" (List.rev_map string_of_int p) in
               Option.fold (fun p prefix -> Format.sprintf "%s:%s" prefix p) p prefix)
        |> Option.map (fun x -> Xml.string_attrib "id" x)
        |> List.of_option
      in

      let data =
        match form with
        | FTrue -> [ mo (UTF8.of_char (UChar.of_int 0x22A4)) ]
        | FFalse -> [ mo (UTF8.of_char (UChar.of_int 0x22A5)) ]
        | FConn (`Not, [ FPred ("_EQ", [ e1; e2 ]) ]) ->
            [ row
                ~a:(thisid (0 :: p))
                (for_expr ?id env (0 :: 0 :: p) e1
                @ [ mo (UTF8.of_char (UChar.of_int 0x2260)) ]
                @ for_expr ?id env (1 :: 0 :: p) e2)
            ]
        | FConn (lg, fs) -> begin
            let xml_lg = [ mo (UTF8.of_char (UChar.of_int (unicode_of_op lg))) ] in

            let xml_fs =
              List.combine fs (assoc_of_op lg)
              |> List.mapi (fun i (f, cmp) ->
                     for_form ~is_pr:(cmp (prio_of_form f) (prio_of_op lg)) env (i :: p) f)
            in

            match (lg, xml_fs) with
            | (`And | `Or | `Imp | `Equiv), [ f1; f2 ] -> f1 @ xml_lg @ f2
            | `Not, [ f ] -> xml_lg @ f
            | (`And | `Or | `Imp | `Not | `Equiv), _ -> assert false
          end
        | FPred ("_EQ", [ e1; e2 ]) ->
            for_expr ?id env (0 :: p) e1 @ [ mo "=" ] @ for_expr ?id env (1 :: p) e2
        | FPred (name, []) -> [ mi (shortname name env.env_prp_name) ]
        | FPred (name, args) ->
            let args = List.mapi (fun i e -> for_expr ?id env (i :: p) e) args in
            [ mi (shortname name env.env_prp_name) ]
            @ [ pr (row (List.flatten (List.join [ mo "," ] args))) ]
        | FBind (bd, x, ty, f) ->
            let bd =
              match bd with
              | `Forall -> UTF8.of_char (UChar.chr 0x2200)
              | `Exist -> UTF8.of_char (UChar.chr 0x2203)
            in

            [ mo bd; mi x; mo ":" ] @ for_type env ty @ [ mo "." ] @ for_form env (0 :: p) f
      in

      [ pr ~doit:is_pr (row ~a:(thisid p) data) ]
    in

    ( (fun ?id env (form : form) -> row (for_form ?id env [] form))
    , (fun ?id env (expr : expr) -> row (for_expr ?id env [] expr))
    , fun env (ty : type_) -> row (for_type env ty) )

  let tomathml ?id env = function `E e -> e_tomathml ?id env e | `F f -> f_tomathml ?id env f
end

(* -------------------------------------------------------------------- *)
module Vars : sig
  val fresh : env -> ?basename:name -> unit -> name
  val push : env -> name * bvar -> env
  val bind : env -> name * type_ -> name * env
  val get : env -> vname -> bvar option
  val modify : env -> vname * bvar -> env
  val remove : env -> vname -> env
  val exists : env -> vname -> bool
  val byid : env -> Handle.t -> (vname * bvar) option
  val getid : env -> vname -> Handle.t option
  val diff : env -> env -> Handle.t list
  val map : env -> (expr option -> expr option) -> env
  val all : env -> (name, bvar list) Map.t
  val to_string : env -> name -> string
  val to_list : env -> (Handle.t * vname * bvar) list
end = struct
  let name_counters : (env, int ref) Map.t ref = ref Map.empty

  (* [fresh env ~basename ()] generates a fresh name for a
     local variable in [env], based on an optional [basename]. *)
  let fresh env ?(basename = "x") () =
    if not (Map.mem basename env.env_var)
    then basename
    else
      let n =
        try Map.find env !name_counters
        with Not_found ->
          let n = ref 0 in
          name_counters := Map.add env n !name_counters;
          n
      in
      let rec aux n =
        let basename = basename ^ string_of_int n in
        if not (Map.mem basename env.env_var) then (basename, n) else aux (n + 1)
      in
      let basename, n' = aux !n in
      n := n';
      basename

  let push (env : env) ((name, (ty, body)) : name * bvar) =
    let i = ref 0 in

    let env_var =
      Map.modify_opt name
        (fun bds ->
          let v = (ty, body) :: Option.default [] bds in
          i := List.length v - 1;
          Some v)
        env.env_var
    in

    let env_handles = BiMap.add (name, !i) (Handle.fresh ()) env.env_handles in

    { env with env_var; env_handles }

  let bind (env : env) ((name, ty) : name * type_) =
    let name = fresh env ~basename:name () in
    (name, push env (name, (ty, None)))

  let get (env : env) ((name, idx) : vname) =
    let bds = Map.find_default [] name env.env_var in
    List.nth_opt bds idx

  let modify (env : env) (((x, i), b) : vname * bvar) =
    let env_var = Map.modify x (List.modify_at i (fun _ -> b)) env.env_var in
    { env with env_var }

  let remove (env : env) ((x, i) : vname) =
    let env_var = Map.modify x (List.remove_at i) env.env_var in
    { env with env_var }

  let exists (env : env) (x : vname) = Option.is_some (get env x)
  let getid env x = BiMap.find_opt x env.env_handles

  let byid env id =
    let open Monad.Option in
    env.env_handles |> BiMap.inverse |> BiMap.find_opt id >>= fun x ->
    get env x >>= fun body -> return (x, body)

  let diff env1 env2 =
    BiMap.vdiff env1.env_handles env2.env_handles |> BiMap.bindings |> List.split |> snd

  let map (env : env) (f : expr option -> expr option) =
    { env with env_var = Map.map (List.map (snd_map f)) env.env_var }

  let all (env : env) = env.env_var

  let to_string env (x : name) =
    let bs = Map.find x env.env_var in
    Printf.sprintf "%s : %s" x
      (List.to_string
         (fun (ty, body) ->
           match body with
           | Some b ->
               Printf.sprintf "%s := %s" (Notation.t_tostring env ty) (Notation.e_tostring env b)
           | None -> Printf.sprintf "%s" (Notation.t_tostring env ty))
         bs)

  let to_list env =
    let open Monad.List in
    Map.bindings env.env_var >>= fun (x, bs) ->
    List.mapi (fun i b -> (Option.get (getid env (x, i)), (x, i), b)) bs
end

(* -------------------------------------------------------------------- *)
module EVars : sig
  val fresh : ?basename:name -> unit -> name
  val push : env -> name option * type_ -> name * env
  val exists : env -> vname -> bool
  val get : env -> vname -> type_ option
  val remove : env -> vname -> env
  val all : env -> (name, type_ list) Map.t
end = struct
  let evar_name_counter = ref (-1)

  (** [fresh ~basename ()] generates a fresh name for an
      existential variable, based on an optional [basename].

      We choose by convention to name existential variables with a leading '?'.
      This ensures freshness by avoiding clashes with variables names input
      by the user, by the definition of identifiers in the lexer. This also
      means that every new existential variable must be instanciated through
      this function. *)
  let fresh ?(basename = "") () =
    incr evar_name_counter;
    "?" ^ basename ^ string_of_int !evar_name_counter

  let push (env : env) ((name, ty) : name option * type_) =
    let name = fresh ?basename:name () in
    ( name
    , { env with
        env_evar = Map.modify_opt name (fun bds -> Some (ty :: Option.default [] bds)) env.env_evar
      } )

  let get (env : env) ((name, idx) : vname) =
    let bds = Map.find_default [] name env.env_evar in
    List.nth_opt bds idx

  let exists (env : env) (x : vname) = Option.is_some (get env x)

  let remove (env : env) ((name, idx) : vname) =
    let bds = Map.find_default [] name env.env_evar in
    let bds = List.remove_at idx bds in
    { env with env_evar = Map.add name bds env.env_evar }

  let all (env : env) = env.env_evar
end

(* -------------------------------------------------------------------- *)
exception RecheckFailure
exception TypingError

(* -------------------------------------------------------------------- *)
module VName : sig
  type bds

  module Map : sig
    val empty : bds
    val push : bds -> name -> name -> bds
  end

  val lindex : bds -> name -> int
  val rindex : bds -> name -> int
  val lfind : bds -> vname -> name
  val rfind : bds -> vname -> name
  val equal : bds -> vname -> vname -> bool
end = struct
  type bds = (name * name) list

  module Map = struct
    let empty : bds = []
    let push (bds : bds) (x : name) (y : name) = (x, y) :: bds
  end

  let lindex (bds : bds) (x : name) : int =
    let rec aux i = function [] -> i | (y, _) :: bds -> aux (i + if x = y then 1 else 0) bds in
    aux 0 bds

  let rindex (bds : bds) (x : name) : int =
    let rec aux i = function [] -> i | (_, y) :: bds -> aux (i + if x = y then 1 else 0) bds in
    aux 0 bds

  let lfind (bds : bds) ((x, i) : vname) =
    let rec aux j = function
      | [] -> raise Not_found
      | (y, z) :: _ when x = y && j = 0 -> z
      | (y, _) :: bds when x = y && j > 0 -> aux (j - 1) bds
      | _ :: bds -> aux j bds
    in
    aux i bds

  let rfind (bds : bds) ((x, i) : vname) =
    let rec aux j = function
      | [] -> raise Not_found
      | (y, z) :: _ when x = z && j = 0 -> y
      | (_, z) :: bds when x = z && j > 0 -> aux (j - 1) bds
      | _ :: bds -> aux j bds
    in
    aux i bds

  let equal (bds : bds) ((n, i) : vname) ((m, j) : vname) =
    (n = m && i - lindex bds n = j - rindex bds m)
    || (i = j && try lfind bds (n, i) = m with Not_found -> false)
end

(* -------------------------------------------------------------------- *)
module Form : sig
  val f_false : form
  val f_true : form
  val f_and : form -> form -> form
  val f_or : form -> form -> form
  val f_imp : form -> form -> form
  val f_equiv : form -> form -> form
  val f_not : form -> form
  val f_ands : form list -> form
  val f_ors : form list -> form
  val f_imps : form list -> form -> form
  val flatten_disjunctions : form -> form list
  val flatten_conjunctions : form -> form list
  val t_unloc : ptype -> type_
  val e_unloc : pexpr -> expr
  val f_unloc : pform -> form
  val parity : logcon -> int
  val tcheck : env -> ptype -> type_
  val trecheck : env -> type_ -> unit
  val einfer : env -> expr -> type_
  val echeck : env -> pexpr -> expr * type_
  val erecheck : env -> type_ -> expr -> unit
  val check : env -> pform -> form
  val recheck : env -> form -> unit
  val t_equal : ?bds:VName.bds -> env -> type_ -> type_ -> bool
  val e_equal : ?bds:VName.bds -> expr -> expr -> bool
  val e_equal_delta : ?bds:VName.bds -> env -> expr -> expr -> bool
  val f_equal : ?bds:VName.bds -> env -> form -> form -> bool
  val equal : ?bds:VName.bds -> env -> term -> term -> bool
  val free_vars : form -> name list
  val e_shift : ?incr:int -> vname -> expr -> expr
  val f_shift : ?incr:int -> vname -> form -> form
  val shift : ?incr:int -> vname -> term -> term
  val shift_under : term -> term -> term
  val direct_subexprs : expr -> expr list
  val direct_subforms : form -> form list
  val direct_subterms : term -> term list
  val modify_direct_subexprs : expr -> expr list -> expr
  val modify_direct_subforms : form -> form list -> form
  val modify_direct_subterms : term -> term list -> term
  val rewrite : ?bds:VName.bds -> env -> term -> term -> term -> term
  val ec_fill : expr -> ectx -> expr
  val ec_concat : ectx -> ectx -> ectx
  val ec_rev : ectx -> ectx
  val fc_is_bound : vname -> fctx -> bool
  val fc_exit : vname -> fctx -> vname
  val fc_fill : form -> fctx -> form
  val fc_concat : fctx -> fctx -> fctx
  val fc_rev : fctx -> fctx

  exception InvalidContextFill of term * ctx

  val c_is_bound : vname -> ctx -> bool
  val c_exit : vname -> ctx -> vname
  val c_fill : term -> ctx -> term
  val c_rev : ctx -> ctx
  val c_push : ictx -> ctx -> ctx
  val fresh_var : ?basename:name -> name list -> name

  module Subst : sig
    type subst

    exception UnboundVariable of vname * subst

    val empty : subst
    val aslist : subst -> (name * sitem) list
    val oflist : (name * sitem) list -> subst
    val fold : ('a -> name * sitem -> 'a) -> 'a -> subst -> 'a
    val add : vname -> expr -> subst -> subst
    val push : name -> sitem -> subst -> subst
    val fetch : vname -> subst -> expr
    val get_tag : vname -> subst -> sitem option
    val is_complete : subst -> bool
    val e_apply1 : vname -> expr -> expr -> expr
    val e_iter : subst -> int -> expr -> expr
    val e_apply : subst -> expr -> expr
    val f_apply1 : vname -> expr -> form -> form
    val f_iter : subst -> int -> form -> form
    val f_apply : subst -> form -> form
    val close : subst -> subst
    val to_string : env -> subst -> string
  end

  val e_unify : env -> LEnv.lenv -> Subst.subst -> expr eqns -> Subst.subst option
  val f_unify : env -> LEnv.lenv -> Subst.subst -> form eqns -> Subst.subst option
end = struct
  let f_and f1 f2 = FConn (`And, [ f1; f2 ])
  let f_or f1 f2 = FConn (`Or, [ f1; f2 ])
  let f_imp f1 f2 = FConn (`Imp, [ f1; f2 ])
  let f_equiv f1 f2 = FConn (`Equiv, [ f1; f2 ])
  let f_not f = FConn (`Not, [ f ])
  let f_false : form = FFalse
  let f_true : form = FTrue

  let f_ands (fs : form list) : form =
    match fs with [] -> f_true | [ f ] -> f | f :: fs -> List.fold_left f_and f fs

  let f_ors (fs : form list) : form =
    match fs with [] -> f_false | [ f ] -> f | f :: fs -> List.fold_left f_or f fs

  let f_imps (fs : form list) (f : form) = List.fold_right f_imp fs f

  let flatten_disjunctions =
    let rec doit acc f =
      match f with FConn (`Or, [ f1; f2 ]) -> doit (f2 :: acc) f1 | _ -> f :: acc
    in
    fun f -> doit [] f

  let flatten_conjunctions =
    let rec doit acc f =
      match f with FConn (`And, [ f1; f2 ]) -> doit (f2 :: acc) f1 | _ -> f :: acc
    in
    fun f -> doit [] f

  let parity (lg : logcon) =
    match lg with `And -> 2 | `Or -> 2 | `Imp -> 2 | `Equiv -> 2 | `Not -> 1

  let t_equal =
    let rec eq_alias (bds : VName.bds) (env : env) (a : vname) (ty : type_) : bool =
      let tgt_a = TVars.get env a in
      let b, tgt_b = match ty with TVar b -> (Some b, TVars.get env b) | _ -> (None, None) in
      match (b, pair_map Monad.Option.concat (tgt_a, tgt_b)) with
      (* Base case *)
      | None, (None, _) -> false (* b is not a var, and a is not an alias *)
      | Some b, (None, None) ->
          VName.equal bds a b (* b is a var, and neither a nor b are aliases *)
      (* Recursive case (either a or b is an alias) *)
      | _, (Some ty', _) -> eq bds env ty ty'
      | _, (_, Some ty') -> eq_alias bds env a ty'
    and eq bds env ty1 ty2 =
      match (ty1, ty2) with
      | TVar ("_dummy", 0), _ | _, TVar ("_dummy", 0) -> true
      | TVar a, ty | ty, TVar a -> eq_alias bds env a ty
      | TUnit, TUnit -> true
      | TProd (tya1, tyb1), TProd (tya2, tyb2) | TOr (tya1, tyb1), TOr (tya2, tyb2) ->
          eq bds env tya1 tya2 && eq bds env tyb1 tyb2
      | TRec (a1, ty1), TRec (a2, ty2) -> eq (VName.Map.push bds a1 a2) env ty1 ty2
      | _, _ -> false
    in

    fun ?(bds = VName.Map.empty) env ty1 ty2 -> eq bds env ty1 ty2

  let e_equal =
    let rec aux bds e1 e2 =
      match (e1, e2) with
      | EVar x1, EVar x2 -> VName.equal bds x1 x2
      | EFun (f1, es1), EFun (f2, es2) when List.length es1 = List.length es2 ->
          f1 = f2 && List.for_all2 (aux bds) es1 es2
      | _, _ -> false
    in
    fun ?(bds = VName.Map.empty) e1 e2 -> aux bds e1 e2

  let e_equal_delta =
    let rec aux bds env e1 e2 =
      match (e1, e2) with
      | EVar x1, EVar x2 when VName.equal bds x1 x2 -> true
      | EVar x1, t | t, EVar x1 -> (
          match Vars.get env x1 with Some (_, Some u) -> aux bds env t u | _ -> false)
      | EFun (f1, es1), EFun (f2, es2) when List.length es1 = List.length es2 ->
          f1 = f2 && List.for_all2 (aux bds env) es1 es2
      | _, _ -> false
    in
    fun ?(bds = VName.Map.empty) env e1 e2 -> aux bds env e1 e2

  let f_equal =
    let rec aux bds env f1 f2 =
      match (f1, f2) with
      | FTrue, FTrue | FFalse, FFalse -> true
      | FPred (p1, es1), FPred (p2, es2) when List.length es1 = List.length es2 ->
          p1 = p2 && List.for_all2 (e_equal ~bds) es1 es2
      | FConn (c1, fs1), FConn (c2, fs2) when List.length fs1 = List.length fs2 ->
          c1 = c2 && List.for_all2 (aux bds env) fs1 fs2
      | FBind (b1, x1, ty1, f1), FBind (b2, x2, ty2, f2) when b1 = b2 ->
          t_equal env ty1 ty2 && aux (VName.Map.push bds x1 x2) env f1 f2
      | _, _ -> false
    in

    fun ?(bds = VName.Map.empty) f1 f2 -> aux bds f1 f2

  let equal ?bds (env : env) (t1 : term) (t2 : term) : bool =
    match (t1, t2) with
    | `F f1, `F f2 -> f_equal ?bds env f1 f2
    | `E e1, `E e2 -> e_equal ?bds e1 e2
    | _ -> false

  let rec free_vars =
    let open Monad.List in
    function
    | FTrue | FFalse -> zero
    | FPred (_, es) -> es >>= e_vars |> List.map name_of_vname
    | FConn (_, fs) -> fs >>= free_vars
    | FBind (_, x, _, f) -> List.remove_all (free_vars f) x

  let rec e_shift ?(incr = 1) ((x, i) : vname) = function
    | EVar (y, j) when x = y && j >= i -> EVar (y, j + incr)
    | EVar _ as e -> e
    | EFun (f, es) -> EFun (f, List.map (e_shift ~incr (x, i)) es)

  (** [f_shift ~incr (x, i) f] increases by [incr] the index of every occurrence of [x]
      in [f] that appears under at least [i] quantifiers that bind [x]. *)
  let rec f_shift ?(incr = 1) ((x, i) : vname) = function
    | (FTrue | FFalse) as f -> f
    | FPred (p, es) -> FPred (p, List.map (e_shift ~incr (x, i)) es)
    | FConn (c, fs) -> FConn (c, List.map (f_shift ~incr (x, i)) fs)
    | FBind (b, y, ty, f) -> FBind (b, y, ty, f_shift ~incr (x, i + if x = y then 1 else 0) f)

  let shift ?incr x = function `E e -> `E (e_shift ?incr x e) | `F f -> `F (f_shift ?incr x f)

  (** [shift_under t u] will shift by 1 the variable x in [u] if [t] starts with
      a binder for x. *)
  let shift_under t u = match t with `F (FBind (_, x, _, _)) -> shift (x, 0) u | _ -> u

  let direct_subforms = function
    | FTrue | FFalse | FPred _ -> []
    | FConn (_, fs) -> fs
    | FBind (_, _, _, f) -> [ f ]

  let direct_subexprs = function EVar _ -> [] | EFun (_, es) -> es

  let direct_subterms : term -> term list = function
    | `F (FPred (_, es)) -> List.map term_of_expr es
    | `F f -> List.map term_of_form (direct_subforms f)
    | `E e -> List.map term_of_expr (direct_subexprs e)

  let modify_direct_subforms f fs =
    match (f, fs) with
    | (FTrue | FFalse | FPred _), _ -> f
    | FConn (c, fs), fs' when List.length fs = List.length fs' -> FConn (c, fs')
    | FBind (b, x, ty, _), [ f ] -> FBind (b, x, ty, f)
    | _ -> raise (Invalid_argument "Wrong arity for new subformulas")

  let modify_direct_subexprs e es =
    match (e, es) with
    | EVar _, _ -> e
    | EFun (f, es), es' when List.length es = List.length es' -> EFun (f, es')
    | _ -> raise (Invalid_argument "Wrong arity for new subexpressions")

  let modify_direct_subterms (t : term) (ts : term list) =
    match t with
    | `F (FPred (p, es)) when List.length es = List.length ts ->
        `F (FPred (p, List.map expr_of_term ts))
    | `F f -> ts |> List.map form_of_term |> modify_direct_subforms f |> term_of_form
    | `E e -> ts |> List.map expr_of_term |> modify_direct_subexprs e |> term_of_expr

  let rec rewrite ?bds env red res (t : term) =
    if equal ?bds env red t
    then res
    else
      direct_subterms t
      |> List.map (rewrite env (shift_under t red) (shift_under t res))
      |> modify_direct_subterms t

  let rec ec_fill e = function
    | [] -> e
    | CFun (name, args, i) :: c ->
        let ls, rs = List.split_at i args in
        EFun (name, ls @ [ ec_fill e c ] @ rs)

  let ec_concat = ( @ )
  let ec_rev = List.rev

  let rec fc_is_bound (x, i) = function
    | [] -> false
    | CBind (_, y, _) :: c ->
        if x = y then if i = 0 then true else fc_is_bound (x, i - 1) c else fc_is_bound (x, i) c
    | _ :: c -> fc_is_bound (x, i) c

  let fc_exit (x, i) =
    let rec aux i = function
      | [] -> i
      | CBind (_, y, _) :: c when x = y -> aux (i - 1) c
      | _ :: c -> aux i c
    in
    fun c -> (x, aux i c)

  let rec fc_fill f = function
    | [] -> f
    | CConn (conn, fs, i) :: c ->
        let ls, rs = List.split_at i fs in
        FConn (conn, ls @ [ fc_fill f c ] @ rs)
    | CBind (b, x, ty) :: c -> FBind (b, x, ty, fc_fill f c)

  let fc_concat = ( @ )
  let fc_rev = List.rev

  let c_is_bound x = function
    | CForm c | CExprPred (c, _, _, _, _) -> fc_is_bound x c
    | CExpr _ -> false

  let c_exit x = function CForm c | CExprPred (c, _, _, _, _) -> fc_exit x c | CExpr _ -> x

  exception InvalidContextFill of term * ctx

  let c_fill t c =
    match (t, c) with
    | `F f, CForm c -> `F (fc_fill f c)
    | `E e, CExpr c -> `E (ec_fill e c)
    | `E e, CExprPred (fc, name, args, i, ec) ->
        let ls, rs = List.split_at i args in
        `F (fc_fill (FPred (name, ls @ [ ec_fill e ec ] @ rs)) fc)
    | _ -> raise (InvalidContextFill (t, c))

  let c_rev = function
    | CForm c -> CForm (fc_rev c)
    | CExpr c -> CExpr (ec_rev c)
    | CExprPred (fc, name, args, i, ec) -> CExprPred (fc_rev fc, name, args, i, ec_rev ec)

  let c_push_e ic = function
    | CExpr c -> CExpr (ic :: c)
    | CExprPred (fc, name, args, i, ec) -> CExprPred (fc, name, args, i, ic :: ec)
    | _ -> raise (Invalid_argument "cannot push expression to formula context")

  let c_push_p (p, args, i) = function
    | CForm fc -> CExprPred (fc, p, args, i, [])
    | _ -> raise (Invalid_argument "cannot push predicate to expression context")

  let c_push_f ic = function
    | CForm c -> CForm (ic :: c)
    | _ -> raise (Invalid_argument "cannot push formula to expression context")

  let c_push ic c =
    match ic with `E e -> c_push_e e c | `P p -> c_push_p p c | `F f -> c_push_f f c | `None -> c

  (* [fresh_var ~basename names] generates a fresh name for a
     variable relative to the ones in [names], based on an optional [basename]. *)
  let fresh_var ?(basename = "x") names =
    if not (List.mem basename names)
    then basename
    else
      let rec aux n =
        let basename = basename ^ string_of_int n in
        if not (List.mem basename names) then basename else aux (n + 1)
      in
      aux 0

  let rec t_unloc (t : ptype) : type_ =
    match unloc t with
    | PTUnit -> TUnit
    | PTVar x -> TVar (unloc x, 0)
    | PTSum (t1, t2) -> TOr (t_unloc t1, t_unloc t2)
    | PTProd (t1, t2) -> TProd (t_unloc t1, t_unloc t2)
    | PTRec (x, t) -> TRec (unloc x, t_unloc t)

  let rec e_unloc (e : pexpr) : expr =
    match unloc e with
    | PEVar (x, i) -> EVar (unloc x, i)
    | PEApp (f, args) -> EFun (unloc f, List.map e_unloc args)

  let rec f_unloc (f : pform) : form =
    let pred name fs = FConn (name, List.map f_unloc fs) in

    match unloc f with
    | PFApp (p, args) -> FPred (unloc p, List.map e_unloc args)
    | PFCst b -> if b then FTrue else FFalse
    | PFAnd (f1, f2) -> pred `And [ f1; f2 ]
    | PFOr (f1, f2) -> pred `Or [ f1; f2 ]
    | PFImp (f1, f2) -> pred `Imp [ f1; f2 ]
    | PFEquiv (f1, f2) -> pred `Equiv [ f1; f2 ]
    | PFNot f1 -> pred `Not [ f1 ]
    | PFForall ((x, ty), f) -> FBind (`Forall, unloc x, t_unloc ty, f_unloc f)
    | PFExists ((x, ty), f) -> FBind (`Exist, unloc x, t_unloc ty, f_unloc f)

  (* FIXME *)
  let rec trecheck (env : env) (ty : type_) : unit =
    match ty with
    | TVar x -> if not (TVars.exists env x) then raise RecheckFailure
    | TUnit -> ()
    | TProd (ty1, ty2) | TOr (ty1, ty2) -> List.iter (trecheck env) [ ty1; ty2 ]
    | TRec (x, ty) -> trecheck (TVars.push env (x, None)) ty

  let rec einfer (env : env) (e : expr) : type_ =
    match e with
    | EVar x -> begin
        match Vars.get env x with None -> raise TypingError | Some (xty, _) -> xty
      end
    | EFun ("_dummy", _) -> TVar ("_dummy", 0)
    | EFun (f, args) -> begin
        match Funs.get env f with
        | None -> raise TypingError
        | Some (fargs, fres) ->
            if List.length fargs <> List.length args then raise TypingError;
            let args = List.map (einfer env) args in
            if not (List.for_all2 (t_equal env) fargs args) then raise TypingError;
            fres
      end

  let rec erecheck (env : env) (ty : type_) (expr : expr) : unit =
    match expr with
    | EVar x ->
        let xty, _ = Option.get_exn (Vars.get env x) RecheckFailure in
        if not (t_equal env ty xty) then raise RecheckFailure
    | EFun (f, args) ->
        let sig_, res = Option.get_exn (Funs.get env f) RecheckFailure in
        if not (t_equal env ty res) then raise RecheckFailure;
        if List.length sig_ <> List.length args then raise RecheckFailure;
        List.iter2 (erecheck env) sig_ args

  let rec recheck (env : env) (form : form) : unit =
    match form with
    | FTrue | FFalse -> ()
    | FPred (name, [ e1; e2 ]) when name = "_EQ" ->
        let t1, t2 =
          begin
            try pair_map (einfer env) (e1, e2) with TypingError -> raise TypingError
          end
        in
        if not (t_equal env t1 t2) then raise RecheckFailure
    | FPred (name, args) -> begin
        let sig_ = Option.get_exn (Prps.get env name) RecheckFailure in
        if List.length sig_ <> List.length args then raise RecheckFailure;
        List.iter2 (erecheck env) sig_ args
      end
    | FConn (lg, forms) ->
        if List.length forms <> parity lg then raise RecheckFailure;
        List.iter (recheck env) forms
    | FBind (_, x, xty, f) ->
        trecheck env xty;
        recheck (Vars.push env (x, (xty, None))) f

  let rec tcheck (env : env) (ty : ptype) =
    match unloc ty with
    | PTUnit -> TUnit
    | PTSum (t1, t2) -> TOr (tcheck env t1, tcheck env t2)
    | PTProd (t1, t2) -> TProd (tcheck env t1, tcheck env t2)
    | PTRec (x, t) -> TRec (unloc x, tcheck (TVars.push env (unloc x, None)) t)
    | PTVar x ->
        if not (TVars.exists env (unloc x, 0)) then raise TypingError;
        TVar (unloc x, 0)

  let echeck (env : env) (e : pexpr) =
    let e = e_unloc e in
    (e, einfer env e)

  let rec check (env : env) (form : pform) =
    let pred name fs = FConn (name, List.map (check env) fs) in

    match unloc form with
    | PFCst true -> FTrue
    | PFCst false -> FFalse
    | PFAnd (f1, f2) -> pred `And [ f1; f2 ]
    | PFOr (f1, f2) -> pred `Or [ f1; f2 ]
    | PFImp (f1, f2) -> pred `Imp [ f1; f2 ]
    | PFEquiv (f1, f2) -> pred `Equiv [ f1; f2 ]
    | PFNot f1 -> pred `Not [ f1 ]
    | PFApp (name, [ e1; e2 ]) when unloc name = "_EQ" ->
        let (e1, t1), (e2, t2) = pair_map (echeck env) (e1, e2) in
        if not (t_equal env t1 t2) then raise TypingError else FPred ("_EQ", [ e1; e2 ])
    | PFApp (name, args) -> begin
        match Prps.get env (unloc name) with
        | None -> raise TypingError
        | Some ar ->
            if List.length args <> List.length ar then raise TypingError;
            let args = List.map (echeck env) args in
            if not (List.for_all2 (t_equal env) ar (List.snd args)) then raise TypingError;
            FPred (unloc name, List.fst args)
      end
    | PFForall ((x, xty), f) ->
        let xty = tcheck env xty in
        let f = check (Vars.push env (unloc x, (xty, None))) f in
        FBind (`Forall, unloc x, xty, f)
    | PFExists ((x, xty), f) ->
        let xty = tcheck env xty in
        let f = check (Vars.push env (unloc x, (xty, None))) f in
        FBind (`Exist, unloc x, xty, f)

  module Subst = struct
    type subst = (name * sitem) list

    let empty = []
    let aslist (s : subst) : _ list = s
    let oflist (s : _ list) : subst = s
    let fold = List.fold_left

    let rec get_tag ((n, i) as x : vname) (s : subst) =
      match s with
      | [] -> None
      | (m, tag) :: s when n = m -> if i = 0 then Some tag else get_tag (n, i - 1) s
      | _ :: s -> get_tag x s

    let flex (x : vname) (s : subst) = get_tag x s = Some Sflex

    let bound (x : vname) (s : subst) =
      match get_tag x s with Some (Sbound _) -> true | _ -> false

    exception UnboundVariable of vname * subst

    let fetch (x : vname) (s : subst) =
      match get_tag x s with Some (Sbound e) -> e | _ -> raise (UnboundVariable (x, s))

    let rec add ((n, i) as x : vname) (e : expr) : subst -> subst = function
      | [] -> failwith "Subst.add [1]"
      | (m, t) :: s when n <> m -> (m, t) :: add x e s
      | (m, t) :: s when n = m && i > 0 -> (m, t) :: add (n, i - 1) e s
      | (m, Sflex) :: s when n = m && i = 0 -> (m, Sbound e) :: s
      | _ -> failwith "Subst.add [2]"

    let push m t s = (m, t) :: s
    let is_complete (s : subst) = List.for_all (fun (_, tag) -> tag <> Sflex) s

    let rec e_apply1 ((x, i) : name * int) (e : expr) (tg : expr) : expr =
      match tg with
      | EVar (y, j) when x = y && i = j -> e
      | EVar (y, j) when x = y && i < j -> EVar (y, j - 1)
      | EVar _ -> tg
      | EFun (f, args) -> EFun (f, List.map (e_apply1 (x, i) e) args)

    let rec f_apply1 ((x, i) : name * int) (e : expr) (f : form) : form =
      match f with
      | FTrue | FFalse -> f
      | FConn (lg, fs) -> FConn (lg, List.map (f_apply1 (x, i) e) fs)
      | FPred (name, args) -> FPred (name, List.map (e_apply1 (x, i) e) args)
      | FBind (bd, y, ty, f) ->
          FBind (bd, y, ty, f_apply1 (x, i + if x = y then 1 else 0) (e_shift (y, i) e) f)

    let rec e_iter s i e =
      if i = 0
      then e
      else
        match s with
        | [] -> assert false
        | (x, Sbound e) :: s -> e_iter s (i - 1) (e_apply1 (x, 0) e e)
        | (_, _) :: s -> e_iter s (i - 1) e

    let rec f_iter s i f =
      if i = 0
      then f
      else
        match s with
        | [] -> assert false
        | (x, Sbound e) :: s -> f_iter s (i - 1) (f_apply1 (x, 0) e f)
        | (_, _) :: s -> f_iter s (i - 1) f

    let e_apply s e = e_iter s (List.length s) e
    let f_apply s f = f_iter s (List.length s) f

    let rec e_close s = function
      | EVar x -> begin try e_close s (fetch x s) with UnboundVariable _ -> EVar x end
      | EFun (f, es) -> EFun (f, List.map (e_close s) es)

    let close s =
      s
      |> List.map
           begin
             fun (x, tag) ->
               let tag = match tag with Sbound e -> Sbound (e_close s e) | _ -> tag in
               (x, tag)
           end

    let to_string env =
      List.to_string ~sep:", " ~left:"{" ~right:"}" (fun (x, tag) ->
          match tag with Sflex -> "?" ^ x | Sbound e -> x ^ " := " ^ Notation.e_tostring env e)
  end

  let rec occurs (x : vname) : expr -> bool = function
    | EVar y when x = y -> true
    | EFun (_, ts) -> List.fold_left (fun b t -> b || occurs x t) false ts
    | _ -> false

  let rec occurs_under ((n, i) as x : vname) : expr -> bool = function
    | EVar (m, j) when n = m && j <= i -> true
    | EFun (_, ts) -> List.fold_left (fun b t -> b || occurs_under x t) false ts
    | _ -> false

  exception Invalid_constant

  (** [e_unify env s eqns] implements a variant of Martelli and Montanari's
      unification algorithm on a list of term equations [eqns], with additional
      handling of a substitution [s] holding the list of bindings and unifiable (or
      "flex") variables, and a local environment [lenv] holding a context of locally
      bound variables. *)
  let rec e_unify (venv : env) (lenv : LEnv.lenv) (s : Subst.subst) = function
    (* success *)
    | [] -> Some (Subst.close s)
    | (t, u) :: eqns -> (
        let unify_cond x t =
          Subst.flex x s
          && (not (occurs x t))
          && (* maybe unnecessary check? *)
          Map.for_all (fun n i -> not (occurs_under (n, i) t)) (LEnv.indices lenv)
        in
        let unify_body x t = e_unify venv lenv (Subst.add x t s) eqns in

        let substitute_cond x = Subst.bound x s in
        let substitute_body x t = e_unify venv lenv s ((Subst.fetch x s, t) :: eqns) in
        let is_const x = match Vars.get venv x with Some (_, Some _) -> true | _ -> false in

        match (t, u) with
        (* (eliminate) is decomposed into the 2 following mutually exclusive cases: *)

        (* (unify) *)
        | EVar x, t when unify_cond x t -> unify_body x t
        | t, EVar x when unify_cond x t -> unify_body x t
        (* (substitute) *)
        | EVar x, t when substitute_cond x -> substitute_body x t
        | t, EVar x when substitute_cond x -> substitute_body x t
        (* (delete) *)
        | EVar x, EVar y when x = y -> e_unify venv lenv s eqns
        (* (decompose) *)
        | EFun (f, ts), EFun (g, us) when f = g -> e_unify venv lenv s (List.combine ts us @ eqns)
        (* (expand) *)
        | t, EVar y when is_const y -> (
            match Vars.get venv y with
            | Some (_, Some ye) -> e_unify venv lenv s ((t, ye) :: eqns)
            | _ -> raise Invalid_constant)
        | EVar x, u when is_const x -> (
            match Vars.get venv x with
            | Some (_, Some xe) -> e_unify venv lenv s ((xe, u) :: eqns)
            | _ -> raise Invalid_constant)
        (* (fail) *)
        | _ -> None)

  (** [f_unify env s eqns] does unification of a list of equations [eqns] between
      formulas, updating along the way a substitution [s] and a local environment [lenv]
      holding a context of locally bound variables.
  *)
  let rec f_unify (venv : env) (lenv : LEnv.lenv) (s : Subst.subst) =
    let open Monad.Option in
    function
    | [] -> Some s
    | (f1, f2) :: eqns -> (
        match (f1, f2) with
        | FTrue, FTrue | FFalse, FFalse -> f_unify venv lenv s eqns
        | FPred (p1, l1), FPred (p2, l2) when p1 = p2 && List.length l1 = List.length l2 ->
            e_unify venv lenv s (List.combine l1 l2) >>= fun s -> f_unify venv lenv s eqns
        | FConn (c1, l1), FConn (c2, l2) when c1 = c2 && List.length l1 = List.length l2 ->
            let subeqns = List.combine l1 l2 in
            f_unify venv lenv s (subeqns @ eqns)
        | FBind (b1, x1, ty1, f1), FBind (b2, x2, ty2, f2) when b1 = b2 && ty1 = ty2 ->
            let f2 = Subst.f_apply1 (x2, 0) (EVar (x1, 0)) (f_shift (x1, 0) f2) in
            f_unify venv (LEnv.enter lenv x1 ty1) s [ (f1, f2) ] >>= fun s ->
            f_unify venv lenv s eqns
        | _ -> None)
end

(* -------------------------------------------------------------------- *)
module Goal : sig
  type entry

  val check_entry : env -> pvar -> entry
  val env_of_entries : pvar list -> env
  val check : pgoal -> env * form list * form
end = struct
  type entry =
    | EPVar of (name * arity)
    | ETFun of (name * sig_)
    | ETVar of (name * bvar)
    | ETTVar of (name * type_ option)

  let check_entry env =
    let for_type = Form.tcheck env in
    let for_expr = Form.echeck env in
    function
    | PProp (name, ar) -> EPVar (unloc name, List.map for_type ar)
    | PFun (name, (ar, ty)) -> ETFun (unloc name, (List.map for_type ar, for_type ty))
    | PVar (name, ty) -> ETVar (unloc name, (for_type ty, None))
    | PExpr (name, body) ->
        let body, ty = for_expr body in
        ETVar (unloc name, (ty, Some body))
    | PTVar name -> ETTVar (unloc name, None)
    | PType (name, ty) -> ETTVar (unloc name, Some (for_type ty))

  let env_of_entries (entries : pvar list) =
    List.fold_left
      (fun env entry ->
        match check_entry env entry with
        | EPVar nmty -> Prps.push env nmty
        | ETFun nmty -> Funs.push env nmty
        | ETVar nmty -> Vars.push env nmty
        | ETTVar nmty -> TVars.push env nmty)
      Env.empty entries

  let check ((ps, hs, f) : pgoal) =
    let env = env_of_entries ps in
    let for_form = Form.check env in
    (env, List.map for_form hs, for_form f)
end

module Translate = struct
  open Api

  (* -------------------------------------------------------------------- *)
  (** From engine to API *)

  let rec of_expr (e : expr) : Logic.expr =
    match e with EVar (x, _) -> Logic.EVar x | EFun (f, es) -> Logic.EFun (f, List.map of_expr es)

  let of_type_ (t : type_) : Logic.type_ =
    match t with
    | TVar (x, _) -> Logic.TVar x
    | _ -> failwith "Fo.Translate.of_type_: unsupported type"

  let of_arity (ar : arity) : Logic.arity = List.map of_type_ ar
  let of_sig_ ((ar, ret) : sig_) : Logic.sig_ = (of_arity ar, of_type_ ret)

  let of_logcon (c : logcon) : Logic.logcon =
    match c with
    | `And -> Logic.And
    | `Or -> Logic.Or
    | `Not -> Logic.Not
    | `Equiv -> Logic.Equiv
    | `Imp -> Logic.Imp

  let of_bkind (b : bkind) : Logic.bkind =
    match b with `Exist -> Logic.Exist | `Forall -> Logic.Forall

  let rec of_form (f : form) : Logic.form =
    match f with
    | FTrue -> Logic.FTrue
    | FFalse -> Logic.FFalse
    | FPred (p, args) -> Logic.FPred (p, List.map of_expr args)
    | FConn (c, fs) -> Logic.FConn (of_logcon c, List.map of_form fs)
    | FBind (b, x, ty, f) -> Logic.FBind (of_bkind b, x, of_type_ ty, of_form f)

  let of_term (t : term) : Logic.term =
    match t with `E expr -> Logic.E (of_expr expr) | `F form -> Logic.F (of_form form)

  let of_bvar ((ty, body) : bvar) : Logic.bvar = (of_type_ ty, Option.map of_expr body)

  let of_env (env : env) : Logic.env =
    let map_to_assoc m f = Map.bindings m |> List.map f in

    let env_sort = map_to_assoc env.env_tvar (fun (x, _) -> x) in

    let env_prp = map_to_assoc env.env_prp (fun (p, ar) -> (p, of_arity ar)) in

    let env_fun = map_to_assoc env.env_fun (fun (f, sig_) -> (f, of_sig_ sig_)) in

    let env_sort_name = map_to_assoc env.env_sort_name identity in

    let env_prp_name = map_to_assoc env.env_prp_name identity in

    let env_fun_name = map_to_assoc env.env_prp_name identity in

    let env_var = map_to_assoc env.env_var (fun (x, bodies) -> (x, bodies |> List.hd |> of_bvar)) in

    { env_sort; env_prp; env_fun; env_sort_name; env_prp_name; env_fun_name; env_var }

  (* -------------------------------------------------------------------- *)
  (** From API to engine *)

  let rec to_expr (e : Logic.expr) : expr =
    match e with Logic.EVar x -> EVar (x, 0) | Logic.EFun (f, es) -> EFun (f, List.map to_expr es)

  let to_type_ (t : Logic.type_) : type_ = match t with Logic.TVar x -> TVar (x, 0)
  let to_arity (ar : Logic.arity) : arity = List.map to_type_ ar
  let to_sig_ ((ar, ret) : Logic.sig_) : sig_ = (to_arity ar, to_type_ ret)
  let to_bvar ((ty, body) : Logic.bvar) : bvar = (to_type_ ty, Option.map to_expr body)

  let to_logcon (c : Logic.logcon) : logcon =
    match c with
    | Logic.And -> `And
    | Logic.Or -> `Or
    | Logic.Not -> `Not
    | Logic.Equiv -> `Equiv
    | Logic.Imp -> `Imp

  let to_bkind (b : Logic.bkind) : bkind =
    match b with Logic.Exist -> `Exist | Logic.Forall -> `Forall

  let rec to_form (f : Logic.form) : form =
    match f with
    | Logic.FTrue -> FTrue
    | Logic.FFalse -> FFalse
    | Logic.FPred (p, args) -> FPred (p, List.map to_expr args)
    | Logic.FConn (c, fs) -> FConn (to_logcon c, List.map to_form fs)
    | Logic.FBind (b, x, ty, f) -> FBind (to_bkind b, x, to_type_ ty, to_form f)

  let to_env (env : Logic.env) : env Hidmap.State.t =
    let assoc_to_map l f = l |> List.map f |> List.enum |> Map.of_enum in

    let env_prp = assoc_to_map env.env_prp (fun (p, ar) -> (p, to_arity ar)) in

    let env_fun = assoc_to_map env.env_fun (fun (f, sig_) -> (f, to_sig_ sig_)) in

    let env_sort_name = assoc_to_map env.env_sort_name identity in

    let env_prp_name = assoc_to_map env.env_prp_name identity in

    let env_fun_name = assoc_to_map env.env_fun_name identity in

    let env_tvar = assoc_to_map env.env_sort (fun x -> (x, [ None ])) in

    let env_var = assoc_to_map env.env_var (fun (x, body) -> (x, [ to_bvar body ])) in

    let open Hidmap.State in
    let* env_handles =
      env_var |> Map.keys |> List.of_enum
      |> fold
           begin
             fun env_handles x ->
               let* hd = Hidmap.push x in
               return (BiMap.add (x, 0) hd env_handles)
           end
           BiMap.empty
    in

    return
      { env_prp
      ; env_fun
      ; env_sort_name
      ; env_prp_name
      ; env_fun_name
      ; env_tvar
      ; env_var
      ; env_evar = Map.empty
      ; env_handles
      }
end
