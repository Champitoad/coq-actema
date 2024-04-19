open Proofview
open CoqUtils
open Api.Utils
open Extlib
open Api

(* -------------------------------------------------------------------- *)
(** * Configuration flags *)

(** ** Debug logging *)

(** Set to true to log the arguments given to the DnD tactics *)
let log_dnd_trace = false

(** Set to true to print the goals exported to Actema *)
let log_goals = false

(** Set to true to print a the terms that fail to get exported to Actema. *)
let log_dummy = false

(* -------------------------------------------------------------------- *)
(** * First-order signatures *)

type symbol =
  | Cst of Names.Constant.t
  | Ctr of Names.constructor
  | Ind of Names.inductive
  | Var of Names.Id.t

module Symbol : sig
  include Map.OrderedType

  val to_string : t -> string
end
with type t = symbol = struct
  type t = symbol

  let to_string = function
    | Cst c -> Names.Constant.to_string c
    | Ctr ((mind, i), j) -> Printf.sprintf "%s_%d_%d" (Names.MutInd.to_string mind) i j
    | Ind (mind, i) -> Printf.sprintf "%s_%d" (Names.MutInd.to_string mind) i
    | Var id -> Names.Id.to_string id

  let compare x y = compare (to_string x) (to_string y)
end

module NameMap = Map.Make (String)

module FOSign = struct
  module SymbolNames = BiMap (Symbol) (String)
  module SymbolMap = Map.Make (Symbol)

  type symbols = SymbolNames.t
  type typing = { t_funcs : Logic.sig_ NameMap.t; t_preds : Logic.arity NameMap.t }
  type t = { symbols : symbols; typing : typing }

  let empty : t =
    { symbols = SymbolNames.empty; typing = { t_funcs = NameMap.empty; t_preds = NameMap.empty } }

  let union (s1 : t) (s2 : t) : t =
    let f _ x _ = Some x in
    { symbols = SymbolNames.union s1.symbols s2.symbols
    ; typing =
        { t_funcs = NameMap.union f s1.typing.t_funcs s2.typing.t_funcs
        ; t_preds = NameMap.union f s1.typing.t_preds s2.typing.t_preds
        }
    }

  let sort_symbols (sign : t) : SymbolNames.t =
    sign.symbols
    |> SymbolNames.filter
         begin
           fun _ n -> not (NameMap.mem n sign.typing.t_funcs || NameMap.mem n sign.typing.t_preds)
         end

  let sort_names (sign : t) : string list = sign |> sort_symbols |> SymbolNames.values
end

let peano : FOSign.t =
  let open FOSign in
  let nat : Logic.type_ = Logic.TVar "nat" in
  let symbols =
    let open SymbolNames in
    empty
    |> add (Ind Trm.Datatypes.nat_name) "nat"
    |> add (Ctr Trm.Datatypes.zero_name) "Z"
    |> add (Ctr Trm.Datatypes.succ_name) "S"
    |> fun m ->
    List.fold_left (fun m name -> add (Cst name) "add" m) m Trm.add_names |> fun m ->
    List.fold_left (fun m name -> add (Cst name) "mult" m) m Trm.mul_names
  in
  let typing =
    let open NameMap in
    let t_funcs =
      empty
      |> add "Z" ([], nat)
      |> add "S" ([ nat ], nat)
      |> add "add" ([ nat; nat ], nat)
      |> add "mult" ([ nat; nat ], nat)
    in
    let t_preds = empty in
    { t_funcs; t_preds }
  in
  { symbols; typing }

(* -------------------------------------------------------------------- *)
(** * Exporting Coq goals to Actema *)

module Export = struct
  (** ** Translating Coq terms to Actema expressions and formulas *)

  let dummy_expr : Logic.expr = Logic.EFun ("_dummy", [])
  let dummy_form : Logic.form = Logic.FPred ("_dummy", [])

  let is_prop env evd term =
    let sort = Retyping.get_sort_of env evd term in
    Sorts.is_prop @@ EConstr.ESorts.kind evd sort

  let is_imp (env, evd) x t1 t2 : bool =
    is_prop env evd t1
    && is_prop (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (x, t1)) env) evd t2
    && (x.Context.binder_name = Names.Anonymous || EConstr.Vars.noccurn evd 1 t2)

  type destenv = { env : Environ.env; evd : Evd.evar_map }
  type destarg = destenv * EConstr.types

  module State = Monads.State (FOSign)
  module Dest = Monads.StateOption (FOSign)

  type 'a sdest = destarg -> 'a Dest.t

  let state_to_dest (m : 'a State.t) : 'a Dest.t =
   fun sign ->
    let res, sign = State.run m sign in
    Some (res, sign)

  let dest_to_state default (m : 'a Dest.t) : 'a State.t =
   fun sign -> match Dest.run m sign with None -> (default, sign) | Some (v, sign) -> (v, sign)

  open FOSign
  open Dest

  let destKO = lift None
  let destwrap (f : 'a -> 'b) (x : 'a) : 'b Dest.t = try return (f x) with Constr.DestKO -> destKO

  let compdest (f : 'a -> 'b Dest.t) (g : 'a -> 'b Dest.t) (x : 'a) : 'b Dest.t =
    let* sign = get in
    match f x sign with
    | Some (v, sign) ->
        let* () = put sign in
        return v
    | None -> g x

  let trydest (f : 'a -> 'b Dest.t) (g : 'a -> 'b State.t) (x : 'a) : 'b State.t =
    let open State in
    let* sign = get in
    match f x sign with
    | Some (v, sign) ->
        let* () = put sign in
        return v
    | None -> g x

  let ( @> ) = compdest
  let ( @>? ) = trydest

  let rec dest_sort (({ evd; _ }, t) : destarg) : unit Dest.t =
    let* sort = destwrap (EConstr.destSort evd) t in
    let sort = EConstr.ESorts.kind evd sort in
    if sort = Sorts.prop then destKO else return ()

  and dest_functy ((({ evd; _ } as e), t) : destarg) : Logic.sig_ Dest.t =
    let rec aux arity t =
      if EConstr.isProd evd t
      then
        let* _, t1, t2 = destwrap (EConstr.destProd evd) t in
        let* sort = find_sort (e, t1) in
        aux (arity @ [ Logic.TVar sort ]) t2
      else
        let* sort = find_sort (e, t) in
        return (arity, Logic.TVar sort)
    in
    aux [] t

  and dest_predty ((({ evd; _ } as e), t) : destarg) : Logic.arity Dest.t =
    let rec aux arity t =
      if EConstr.isProd evd t
      then
        let* _, t1, t2 = destwrap (EConstr.destProd evd) t in
        let* sort = find_sort (e, t1) in
        aux (arity @ [ Logic.TVar sort ]) t2
      else
        let* sort = t |> EConstr.to_constr evd |> destwrap Constr.destSort in
        if Sorts.is_prop sort then return arity else destKO
    in
    aux [] t

  and add_sort name sy ty (e : destenv) : unit Dest.t =
    let* () = dest_sort (e, ty) in
    let* sign = get in
    let symbols = SymbolNames.add sy name sign.symbols in
    put { sign with symbols }

  and add_func ?(strict = false) name sy ty (e : destenv) : unit Dest.t =
    let* sig_ = dest_functy (e, ty) in
    if strict && List.length (fst sig_) = 0
    then destKO
    else
      let* sign = get in
      let symbols = SymbolNames.add sy name sign.symbols in
      let t_funcs = NameMap.add name sig_ sign.typing.t_funcs in
      let typing = { sign.typing with t_funcs } in
      put { symbols; typing }

  and add_pred name sy ty (e : destenv) : unit Dest.t =
    let* arity = dest_predty (e, ty) in
    let* sign = get in
    let symbols = SymbolNames.add sy name sign.symbols in
    let t_preds = NameMap.add name arity sign.typing.t_preds in
    let typing = { sign.typing with t_preds } in
    put { symbols; typing }

  and add_symbol ?(strict = false) name sy ty e : unit Dest.t =
    begin
      add_sort name sy ty @> add_func ~strict name sy ty @> add_pred name sy ty
      @> fun _ -> return ()
    end
      e

  and add_symbol_lazy ?(strict = false) sy (info : unit -> string * EConstr.t) e : unit Dest.t =
    let* sign = get in
    if not (SymbolNames.mem sy sign.symbols)
    then
      let name, ty = info () in
      add_symbol ~strict name sy ty e
    else return ()

  and find_sort (d : destarg) : string Dest.t =
    let* sy = dest_symbol d in
    let* sign = get in
    match SymbolNames.find_opt sy (sort_symbols sign) with
    | Some name -> return name
    | None -> destKO

  and find_func (d : destarg) : (Logic.name * Logic.sig_) Dest.t =
    let* sy = dest_symbol d in
    let* sign = get in
    match SymbolNames.find_opt sy sign.symbols with
    | Some name -> begin
        match NameMap.find_opt name sign.typing.t_funcs with
        | Some arity -> return (name, arity)
        | None -> destKO
      end
    | None -> destKO

  and find_pred (d : destarg) : (Logic.name * Logic.arity) Dest.t =
    let* sy = dest_symbol d in
    let* sign = get in
    match SymbolNames.find_opt sy sign.symbols with
    | Some name -> begin
        match NameMap.find_opt name sign.typing.t_preds with
        | Some arity -> return (name, arity)
        | None -> destKO
      end
    | None -> destKO

  and dest_sconst : symbol sdest =
   fun (({ env; evd } as e), t) ->
    let* cst, _ = destwrap (EConstr.destConst evd) t in
    let sy = Cst cst in
    let* () =
      let info () =
        let name = Names.Constant.to_string cst in
        let c = Environ.lookup_constant cst env in
        let ty = c.const_type |> EConstr.of_constr in
        (name, ty)
      in
      add_symbol_lazy sy info e
    in
    return sy

  and dest_sconstruct : symbol sdest =
   fun (({ env; evd } as e), t) ->
    let* ctr, _ = destwrap (EConstr.destConstruct evd) t in
    let sy = Ctr ctr in
    let* () =
      let info () =
        let name = kname_of_constructor env ctr |> Names.KerName.to_string in
        let ty = type_of_constructor env ctr in
        (name, ty)
      in
      add_symbol_lazy sy info e
    in
    return sy

  and dest_sind : symbol sdest =
   fun (({ env; evd } as e), t) ->
    let* ind, _ = destwrap (EConstr.destInd evd) t in
    let sy = Ind ind in
    let* () =
      let info () =
        let name = kname_of_inductive env ind |> Names.KerName.to_string in
        let ty = arity_of_inductive env ind in
        (name, ty)
      in
      add_symbol_lazy sy info e
    in
    return sy

  and dest_svar : symbol sdest =
   fun (({ env; evd } as e), t) ->
    let* id = destwrap (EConstr.destVar evd) t in
    let sy = Var id in
    let* () =
      let info () =
        let name = Names.Id.to_string id in
        let ty =
          Environ.lookup_named id env |> Context.Named.Declaration.get_type |> EConstr.of_constr
        in
        (name, ty)
      in
      add_symbol_lazy ~strict:true sy info e
    in
    return sy

  and dest_symbol : symbol sdest =
   fun et ->
    begin
      dest_sconst @> dest_sconstruct @> dest_sind @> dest_svar
    end
      et

  type edest = Logic.expr sdest

  let rec dest_econst : edest =
   fun (e, t) ->
    let* name, sig_ = find_func (e, t) in
    match sig_ with [], _ -> return (Logic.EFun (name, [])) | _ -> destKO

  and dest_evar : edest =
   fun ({ env; evd; _ }, t) ->
    let* id = destwrap (EConstr.destVar evd) t in
    let name = Names.Id.to_string id in
    return (Logic.EVar name)

  and dest_erel : edest =
   fun ({ env; evd; _ }, t) ->
    let* n = destwrap (EConstr.destRel evd) t in
    let name =
      EConstr.lookup_rel n env |> EConstr.to_rel_decl evd |> Context.Rel.Declaration.get_name
    in
    match name with Name id -> return (Logic.EVar (Names.Id.to_string id)) | _ -> destKO

  and dest_eapp : edest =
   fun (({ evd; _ } as e), t) ->
    let* head, args = destwrap (EConstr.destApp evd) t in
    let* name, _ = find_func (e, head) in
    let* targs = args |> Array.to_list |> State.map (fun u -> dest_expr (e, u)) |> state_to_dest in
    return (Logic.EFun (name, targs))

  and dest_edummy : destarg -> Logic.expr State.t =
   fun ({ env; evd; _ }, t) ->
    if log_dummy
    then
      Log.str
      @@ Format.sprintf "Failed to translate expression:\n%s" (Log.string_of_econstr env evd t);
    State.return dummy_expr

  and dest_expr : destarg -> Logic.expr State.t =
   fun et ->
    begin
      dest_econst @>? dest_evar @>? dest_erel @>? dest_eapp @>? dest_edummy
    end
      et

  type fdest = Logic.form sdest

  let rec dest_pconst : fdest =
   fun (({ env; evd; _ } as e), t) ->
    if not (is_prop env evd t)
    then destKO
    else
      let* name, _ = find_pred (e, t) in
      return (Logic.FPred (name, []))

  and dest_pvar : fdest =
   fun ({ env; evd; _ }, t) ->
    if not (is_prop env evd t)
    then destKO
    else
      let* id = destwrap (EConstr.destVar evd) t in
      let name = Names.Id.to_string id in
      return (Logic.FPred (name, []))

  and dest_papp : fdest =
   fun (({ env; evd; _ } as e), t) ->
    if not (is_prop env evd t)
    then destKO
    else
      let* head, args = destwrap (EConstr.destApp evd) t in
      let* name, _ = find_pred (e, head) in
      let* targs =
        args |> Array.to_list |> State.map (fun u -> dest_expr (e, u)) |> state_to_dest
      in
      Dest.return (Logic.FPred (name, targs))

  and dest_eq : fdest =
   fun (({ env; evd; _ } as e), t) ->
    let* head, args = destwrap (EConstr.destApp evd) t in
    let* ind, _ = destwrap (EConstr.destInd evd) head in
    match (Trm.Logic.eq_ind ind "eq", args) with
    | true, [| t; t1; t2 |] ->
        (* Check we are not equating two propositions. *)
        let* () =
          try
            let sort = EConstr.destSort evd t in
            let sort = EConstr.ESorts.kind evd sort in
            if sort = Sorts.prop then destKO else return ()
          with destKO -> return ()
        in
        (* Destruct the two sides of the equality. *)
        let* e1 = dest_expr (e, t1) |> state_to_dest in
        let* e2 = dest_expr (e, t2) |> state_to_dest in
        return (Logic.FPred ("_EQ", [ e1; e2 ]))
    | _ -> destKO

  and dest_true : fdest =
   fun ({ env; evd; _ }, t) ->
    let* ind, _ = destwrap (EConstr.destInd evd) t in
    if Trm.Logic.eq_ind ind "True" then return Logic.FTrue else destKO

  and dest_false : fdest =
   fun ({ env; evd; _ }, t) ->
    let* ind, _ = destwrap (EConstr.destInd evd) t in
    if Trm.Logic.eq_ind ind "False" then return Logic.FFalse else destKO

  and dest_imp : fdest =
   fun (({ env; evd; _ } as e), t) ->
    let* x, t1, t2 = destwrap (EConstr.destProd evd) t in
    if not (is_imp (env, evd) x t1 t2)
    then destKO
    else
      let env = EConstr.push_rel (Context.Rel.Declaration.LocalAssum (x, t1)) env in
      let* f1 = dest_form (e, t1) |> state_to_dest in
      let* f2 = dest_form ({ e with env }, t2) |> state_to_dest in
      return (Logic.FConn (Logic.Imp, [ f1; f2 ]))

  and dest_and : fdest =
   fun (({ env; evd; _ } as e), t) ->
    let* head, args = destwrap (EConstr.destApp evd) t in
    let* ind, _ = destwrap (EConstr.destInd evd) head in
    match (Trm.Logic.eq_ind ind "and", args) with
    | true, [| t1; t2 |] ->
        let* f1 = dest_form (e, t1) |> state_to_dest in
        let* f2 = dest_form (e, t2) |> state_to_dest in
        return (Logic.FConn (Logic.And, [ f1; f2 ]))
    | _ -> destKO

  and dest_or : fdest =
   fun (({ env; evd; _ } as e), t) ->
    let* head, args = destwrap (EConstr.destApp evd) t in
    let* ind, _ = destwrap (EConstr.destInd evd) head in
    match (Trm.Logic.eq_ind ind "or", args) with
    | true, [| t1; t2 |] ->
        let* f1 = dest_form (e, t1) |> state_to_dest in
        let* f2 = dest_form (e, t2) |> state_to_dest in
        return (Logic.FConn (Logic.Or, [ f1; f2 ]))
    | _ -> destKO

  and dest_iff : fdest =
   fun (({ evd; _ } as e), t) ->
    let* head, args = destwrap (EConstr.destApp evd) t in
    let* sy = dest_sconst (e, head) in
    match sy with
    | Cst cst ->
        let not_cst = Names.Constant.make1 (kername Trm.Logic.path "iff") in
        begin
          match (Names.eq_constant_key cst not_cst, args) with
          | true, [| t1; t2 |] ->
              let* f1 = dest_form (e, t1) |> state_to_dest in
              let* f2 = dest_form (e, t2) |> state_to_dest in
              return (Logic.FConn (Logic.Equiv, [ f1; f2 ]))
          | _ -> destKO
        end
    | _ -> destKO

  and dest_not : fdest =
   fun (({ evd; _ } as e), t) ->
    let* head, args = destwrap (EConstr.destApp evd) t in
    let* sy = dest_sconst (e, head) in
    match sy with
    | Cst cst ->
        let not_cst = Names.Constant.make1 (kername Trm.Logic.path "not") in
        begin
          match (Names.eq_constant_key cst not_cst, args) with
          | true, [| t1 |] ->
              let* f1 = dest_form (e, t1) |> state_to_dest in
              return (Logic.FConn (Logic.Not, [ f1 ]))
          | _ -> destKO
        end
    | _ -> destKO

  and dest_forall : fdest =
   fun (({ env; evd; _ } as e), t) ->
    let* x, t1, t2 = destwrap (EConstr.destProd evd) t in
    let* sort = find_sort (e, t1) in
    match Context.binder_name x with
    | Name id ->
        let name = Names.Id.to_string id in
        let ty = Logic.TVar sort in
        let env = EConstr.push_rel (Context.Rel.Declaration.LocalAssum (x, t1)) env in
        let* body = dest_form ({ e with env }, t2) |> state_to_dest in
        return (Logic.FBind (Logic.Forall, name, ty, body))
    | _ -> destKO

  and dest_exists : fdest =
   fun (({ env; evd; _ } as e), t) ->
    let* head, args = destwrap (EConstr.destApp evd) t in
    let* ind, _ = destwrap (EConstr.destInd evd) head in
    match (Trm.Logic.eq_ind ind "ex", args) with
    | true, [| _; t2 |] ->
        let* x, t1, t2 = destwrap (EConstr.destLambda evd) t2 in
        let* sort = find_sort (e, t1) in
        begin
          match Context.binder_name x with
          | Name id ->
              let name = Names.Id.to_string id in
              let ty = Logic.TVar sort in
              let env = EConstr.push_rel (Context.Rel.Declaration.LocalAssum (x, t1)) env in
              let* body = dest_form ({ e with env }, t2) |> state_to_dest in
              return (Logic.FBind (Logic.Exist, name, ty, body))
          | _ -> destKO
        end
    | _ -> destKO

  and dest_dummy : destarg -> Logic.form State.t =
   fun ({ env; evd; _ }, t) ->
    if log_dummy
    then
      Log.str @@ Format.sprintf "Failed to translate formula:\n%s" (Log.string_of_econstr env evd t);
    State.return dummy_form

  and dest_form : destarg -> Logic.form State.t =
   fun et ->
    begin
      dest_imp @>? dest_forall @>? dest_eq @>? dest_exists @>? dest_and @>? dest_or @>? dest_iff
      @>? dest_not @>? dest_true @>? dest_false @>? dest_papp @>? dest_pconst @>? dest_pvar
      @>? dest_dummy
    end
      et

  (** ** Translating Coq's global and local environments to an Actema environment *)

  (* Local environment of Actema definitions *)
  type varenv = Logic.bvar NameMap.t
  type varsign = varenv * FOSign.t

  let shortname (fullname : string) : string =
    fullname |> String.split_on_char '.' |> List.rev |> List.hd

  let env_of_varsign ((venv, sign) : varsign) : Logic.env =
    let open FOSign in
    let env_sort = "_dummy" :: sort_names sign in
    let env_sort_name = List.(combine env_sort (map shortname env_sort)) in

    let func_names = sign.typing.t_funcs |> NameMap.bindings |> List.split |> fst in
    let env_fun =
      ("_dummy", ([], Logic.TVar "_dummy"))
      :: List.map (fun f -> (f, NameMap.find f sign.typing.t_funcs)) func_names
    in
    let env_fun_name = List.(combine func_names (map shortname func_names)) in

    let pred_names = sign.typing.t_preds |> NameMap.bindings |> List.split |> fst in
    let env_prp =
      ("_dummy", []) :: List.map (fun p -> (p, NameMap.find p sign.typing.t_preds)) pred_names
    in
    let env_prp_name = List.(combine pred_names (map shortname pred_names)) in

    let env_var = NameMap.bindings venv in

    { env_sort; env_sort_name; env_fun; env_fun_name; env_prp; env_prp_name; env_var }

  let add_var name ty value ({ env; evd } as e : destenv) (venv : varenv) : varenv Dest.t =
    let* sort = find_sort (e, ty) in
    let* body =
      match value with
      | None -> return None
      | Some v ->
          let* body = dest_expr (e, EConstr.of_constr v) |> state_to_dest in
          return (Some body)
    in
    return (NameMap.add name (Logic.TVar sort, body) venv)

  let local_env ({ env = coq_env; _ } as e : destenv) : varenv State.t =
    (* Add sorts, default elements, functions, predicates and variables defined
       as local variables *)
    State.fold
      begin
        fun venv decl ->
          let id = Context.Named.Declaration.get_id decl in
          let name = id |> Names.Id.to_string in
          let ty = decl |> Context.Named.Declaration.get_type |> EConstr.of_constr in
          let value = Context.Named.Declaration.get_value decl in

          let open State in
          let* () =
            begin
              add_sort name (Var id) ty
              @>? add_func ~strict:true name (Var id) ty
              @>? add_pred name (Var id) ty
              @>? fun _ -> return ()
            end
              e
          in

          let* venv =
            begin
              add_var name ty value e @>? return
            end
              venv
          in

          return venv
      end
      NameMap.empty (Environ.named_context coq_env)

  (** Does an expression contain [_dummy] as a sub-expression ? *)
  let rec expr_contains_dummy expr : bool =
    match expr with
    | Logic.EVar name -> false
    | Logic.EFun (f, exprs) ->
        (f = "_dummy" && List.length exprs = 0) || List.exists expr_contains_dummy exprs

  (** Does a formula contain [_dummy] as a sub-formula or sub-expression ? *)
  let rec form_contains_dummy form : bool =
    match form with
    | Logic.FTrue | Logic.FFalse -> false
    | Logic.FPred (name, exprs) ->
        (name = "_dummy" && List.length exprs = 0) || List.exists expr_contains_dummy exprs
    | Logic.FConn (conn, forms) -> List.exists form_contains_dummy forms
    | Logic.FBind (kind, x, ty, f) -> form_contains_dummy f

  (** Split a module path into a directory path and the rest. *)
  let rec split_mpath mpath =
    match mpath with
    | Names.ModPath.MPfile dirpath ->
        (List.rev_map Names.Id.to_string (Names.DirPath.repr dirpath), [])
    | Names.ModPath.MPdot (mpath, label) ->
        let dirpath, rest = split_mpath mpath in
        (dirpath, rest @ [ Names.Label.to_string label ])
    | Names.ModPath.MPbound _ ->
        (* Functor arguments are not supported (yet). *)
        raise @@ Invalid_argument "split_mpath"

  (** Encode the full name of a lemma. *)
  let encode_lemma_name (name : Names.Constant.t) : string option =
    try
      let dirpath, modpath = split_mpath @@ Names.Constant.modpath name in
      let res =
        Format.sprintf "C%s/%s/%s"
          (List.to_string ~sep:"." ~left:"" ~right:"" Fun.id dirpath)
          (List.to_string ~sep:"." ~left:"" ~right:"" Fun.id modpath)
          (Names.Label.to_string @@ Names.Constant.label name)
      in
      Some res
    with Invalid_argument _ -> None

  (** Encode the name of an inductive constructor that we want to use as a lemma. *)
  let encode_constructor_name (name : Names.Construct.t) : string option =
    try
      let (name, i), j = name in
      let dirpath, modpath = split_mpath @@ Names.MutInd.modpath name in
      let res =
        Format.sprintf "I%s/%s/%s/%d/%d"
          (List.to_string ~sep:"." ~left:"" ~right:"" Fun.id dirpath)
          (List.to_string ~sep:"." ~left:"" ~right:"" Fun.id modpath)
          (Names.Label.to_string @@ Names.MutInd.label name)
          i j
      in
      Some res
    with Invalid_argument _ -> None

  (** Collect all the lemmas from coq_env.env_globals.constants we can translate to Actema. *)
  let constant_lemmas ({ env = coq_env; evd } as e : destenv) : Logic.lemma list State.t =
    let g_consts =
      (Environ.Globals.view coq_env.env_globals).constants |> Names.Cmap_env.bindings
      (*|> List.filter begin fun (cname, _) ->
            let target = Names.Constant.make1 (kername ["Actema"; "Test"] "my_add0") in
            Names.Constant.CanOrd.equal cname target
         end*)
      (*|> List.take 100*)
    in
    State.fold
      begin
        fun lemmas (id, (ckey, _)) ->
          let open State in
          (* First check whether we can encode the lemma name. *)
          begin
            match encode_lemma_name id with
            | None -> return lemmas
            | Some l_full ->
                let l_user = id |> Names.Constant.label |> Names.Label.to_string in
                let ty = ckey.Declarations.const_type |> EConstr.of_constr in
                let* l_stmt = dest_form (e, ty) in

                (* Check we did indeed manage to translate the lemma.
                   Discard the lemma if it is not the case. *)
                if not (form_contains_dummy l_stmt)
                then return @@ (Logic.{ l_user; l_full; l_stmt } :: lemmas)
                else return lemmas
          end
      end
      [] g_consts

  (** Collect all the lemmas from coq_env.env_globals.inductives we can translate to Actema. *)
  let constructor_lemmas ({ env = coq_env; evd } as e : destenv) : Logic.lemma list State.t =
    let g_constructs =
      (* Get the list of all mutual inductives. *)
      (Environ.Globals.view coq_env.env_globals).inductives |> Names.Mindmap_env.bindings
      (* Get the list of all inductives.
         Inductives in a block are indexed starting at 0. *)
      |> List.concat_map
           begin
             fun (mind_name, (mind_body, _)) ->
               List.init mind_body.Declarations.mind_ntypes @@ fun i ->
               ((mind_name, i), mind_body.Declarations.mind_packets.(i))
           end
      (* Get the list of all inductive constructors (with their type).
         Constructors in an inductive are indexed starting at 1. *)
      |> List.concat_map
           begin
             fun (ind_name, ind_body) ->
               ind_body.Declarations.mind_user_lc |> Array.to_list
               |> List.mapi (fun j ty -> (ind_body, (ind_name, j + 1), ty))
           end
      (*|> List.take 100*)
    in
    State.fold
      begin
        fun lemmas (ind_body, constr_name, constr_type) ->
          let open State in
          (* First check whether we can encode the constructor name. *)
          begin
            match encode_constructor_name constr_name with
            | None -> return lemmas
            | Some l_full ->
                let _, j = constr_name in
                let l_user = ind_body.Declarations.mind_consnames.(j - 1) |> Names.Id.to_string in
                let ty = constr_type |> EConstr.of_constr in
                let* l_stmt = dest_form (e, ty) in

                (* Check we did indeed manage to translate the constructor's type.
                   Discard the lemma if it is not the case. *)
                if not (form_contains_dummy l_stmt)
                then
                  (*(Log.str @@ Format.sprintf "Translated constructor : %s --> %s"
                    l_full
                    (Utils.string_of_form l_stmt);*)
                  return @@ (Logic.{ l_user; l_full; l_stmt } :: lemmas)
                else return lemmas
          end
      end
      [] g_constructs

  let hyps ({ env = coq_env; evd } as e : destenv) : Logic.hyp list State.t =
    State.fold
      begin
        fun hyps decl ->
          let name = Context.Named.Declaration.get_id decl in
          let ty = decl |> Context.Named.Declaration.get_type |> EConstr.of_constr in
          dest_to_state hyps
            begin
              let open Dest in
              if is_prop coq_env evd ty
              then
                let h_id = Names.Id.to_string name in
                let* h_form = dest_form (e, ty) |> state_to_dest in
                let hyp = Logic.{ h_id; h_form } in
                return (hyps @ [ hyp ])
              else return hyps
            end
      end
      [] (Environ.named_context coq_env)

  (** [goal env sign gl] exports the Coq goal [gl] into an Actema goal and a
     mapping from Actema uids to Coq identifiers *)
  let goal (goal : Goal.t) (init_sign : FOSign.t) : Logic.goal * FOSign.t =
    let coq_env = Goal.env goal in
    let evd = Goal.sigma goal in
    let concl = Goal.concl goal in

    let e = { env = coq_env; evd } in

    let open State in
    let goal =
      let* varenv = local_env e in
      let* g_hyps = hyps e in
      let* g_concl = dest_form (e, concl) in

      let* sign = get in
      let g_env = env_of_varsign (varenv, sign) in

      return Logic.{ g_env; g_hyps; g_concl }
    in

    let goal, sign = run goal init_sign in
    if log_goals
    then begin
      (*Log.str (List.to_string (fun (f, _) -> f) goal.g_env.env_fun);
        Log.str ( Utils.string_of_form goal.g_concl);*)
      Log.str (Logic.show_goal goal)
    end;
    (goal, sign)

  (** Get the list of all lemmas we can export to actema. *)
  let lemmas (goal : Goal.t) (init_sign : FOSign.t) : Logic.lemma list * FOSign.t =
    State.run
      begin
        let open State in
        let destenv = { env = Goal.env goal; evd = Goal.sigma goal } in
        let start = Sys.time () in
        let* l1 = constant_lemmas destenv in
        let middle = Sys.time () in
        let* l2 = constructor_lemmas destenv in
        let stop = Sys.time () in
        Log.str
        @@ Format.sprintf "Time to export lemmas: %.2fs (constants) and %.2fs (inductives)"
             (middle -. start) (stop -. middle);
        Log.str
        @@ Format.sprintf "Succesfully exported lemmas: %d (constants) and %d (inductives)"
             (List.length l1) (List.length l2);
        return (l1 @ l2)
      end
      init_sign
end

(* -------------------------------------------------------------------- *)
(** * Importing Actema actions as Coq tactics *)

module Import = struct
  (* let kname = kername ["Actema"; "DnD"] *)
  let kname = kername [ "Actema"; "HOL" ]

  let symbol (sy : symbol) : EConstr.t =
    match sy with
    | Cst c -> EConstr.UnsafeMonomorphic.mkConst c
    | Ctr c -> EConstr.UnsafeMonomorphic.mkConstruct c
    | Ind i -> EConstr.UnsafeMonomorphic.mkInd i
    | Var x -> EConstr.mkVar x

  let sort_index (sign : FOSign.t) (s : string) : int =
    FOSign.sort_symbols sign |> FOSign.SymbolNames.values |> List.nth_index 0 s

  let infer_sort (env : Logic.env) (e : Logic.expr) : string =
    match einfer env e with Logic.TVar name -> name

  let tdyn_ty () : EConstr.t = EConstr.UnsafeMonomorphic.mkInd (Names.MutInd.make1 (kname "TDYN"), 0)

  let tdyn sort =
    let open EConstr in
    let tdyn = UnsafeMonomorphic.mkConstruct ((Names.MutInd.make1 (kname "TDYN"), 0), 1) in
    mkApp (tdyn, [| sort |])

  let sorts env (sign : FOSign.t) : EConstr.t =
    FOSign.sort_symbols sign |> FOSign.SymbolNames.keys
    |> List.map (fun sort_sy -> tdyn (symbol sort_sy))
    |> Trm.Datatypes.of_list env (tdyn_ty ()) identity

  let sort_ty ts (s : EConstr.t) : EConstr.t =
    let name = Names.Constant.make1 (kname "sort") in
    let ty = EConstr.UnsafeMonomorphic.mkConst name in
    EConstr.mkApp (ty, [| ts; s |])

  let env_ty ts () : EConstr.t =
    let name = Names.Constant.make1 (kname "env") in
    let ty = EConstr.UnsafeMonomorphic.mkConst name in
    EConstr.mkApp (ty, [| ts |])

  let clos_ty ts () : EConstr.t =
    let open EConstr in
    let sort_s = sort_ty ts (Trm.mkVar "s") in
    mkArrowR (env_ty ts ()) (mkArrowR (env_ty ts ()) sort_s)

  let inst1_ty ts () : EConstr.t =
    let name = Names.Constant.make1 (kname "inst1") in
    let ty = EConstr.UnsafeMonomorphic.mkConst name in
    EConstr.mkApp (ty, [| ts |])

  let type_ (sign : FOSign.t) (ty : Logic.type_) : EConstr.t =
    match ty with Logic.TVar x -> symbol (FOSign.SymbolNames.dnif x sign.symbols)

  let rec expr (sign : FOSign.t) (lenv : Logic.lenv) (e : Logic.expr) : EConstr.t =
    match e with
    | Logic.EVar x ->
        if LEnv.exists lenv x
        then begin
          let index : int = List.(lenv |> split |> fst |> nth_index 0 x) in
          EConstr.mkRel (index + 1)
        end
        else Trm.mkVar x
    | Logic.EFun (f, args) ->
        let head = symbol (FOSign.SymbolNames.dnif f sign.symbols) in
        let args = List.map (expr sign lenv) args in
        EConstr.mkApp (head, Array.of_list args)

  let rec expr_itrace coq_env (sign : FOSign.t) (env : Logic.env) (lenv : Logic.lenv) (side : int)
      (e : Logic.expr) : EConstr.t =
    match e with
    | Logic.EVar x ->
        if LEnv.exists lenv x
        then begin
          let s = sort_index sign (infer_sort (Utils.Vars.push_lenv env lenv) e) in
          let index : int = List.(lenv |> split |> fst |> nth_index 0 x) in
          let env_index = if side = 0 then 2 else 1 in
          EConstr.(
            mkApp (mkRel env_index, Trm.Datatypes.[| of_nat coq_env s; of_nat coq_env index |]))
        end
        else Trm.mkVar x
    | Logic.EFun (f, args) ->
        let head = symbol (FOSign.SymbolNames.dnif f sign.symbols) in
        let args = List.map (expr_itrace coq_env sign env lenv side) args in
        EConstr.mkApp (head, Array.of_list args)

  let rec form coq_env sigma (sign : FOSign.t) (env : Logic.env) (lenv : Logic.lenv)
      (f : Logic.form) : EConstr.t =
    let form = form coq_env sigma sign env in
    match f with
    | Logic.FPred ("_EQ", [ t1; t2 ]) ->
        let ty = einfer (Vars.push_lenv env lenv) t1 |> type_ sign in
        let t1 = expr sign lenv t1 in
        let t2 = expr sign lenv t2 in
        EConstr.mkApp (Trm.Logic.eq coq_env ty, [| t1; t2 |])
    | Logic.FPred (p, args) ->
        let head = symbol (FOSign.SymbolNames.dnif p sign.symbols) in
        let args = List.map (expr sign lenv) args in
        EConstr.mkApp (head, Array.of_list args)
    | Logic.FTrue -> Trm.Logic.true_ coq_env
    | Logic.FFalse -> Trm.Logic.false_ coq_env
    | Logic.FConn (Logic.And, [ f1; f2 ]) -> Trm.Logic.and_ coq_env (form lenv f1) (form lenv f2)
    | Logic.FConn (Logic.Or, [ f1; f2 ]) -> Trm.Logic.or_ coq_env (form lenv f1) (form lenv f2)
    | Logic.FConn (Logic.Imp, [ f1; f2 ]) -> Trm.Logic.imp (form lenv f1) (form lenv f2)
    | Logic.FConn (Logic.Equiv, [ f1; f2 ]) -> Trm.Logic.iff coq_env (form lenv f1) (form lenv f2)
    | Logic.FConn (Logic.Not, [ f1 ]) -> Trm.Logic.not coq_env (form lenv f1)
    | Logic.FBind (Logic.Forall, x, typ, body) ->
        let ty = type_ sign typ in
        let lenv = LEnv.enter lenv x typ in
        Trm.Logic.fa x ty (form lenv body)
    | Logic.FBind (Logic.Exist, x, typ, body) ->
        let ty = type_ sign typ in
        let lenv = LEnv.enter lenv x typ in
        Trm.Logic.ex coq_env sigma x ty (form lenv body)
    | _ -> failwith "Unsupported formula"

  let boollist_of_intlist = Stdlib.List.map (fun n -> if n = 0 then false else true)

  let itrace coq_env sigma ts (sign : FOSign.t) (env : Logic.env) (mode : [ `Back | `Forw ])
      (lp : int list) (rp : int list) (lf : Logic.form) (rf : Logic.form) (itr : Logic.itrace) :
      bool list * EConstr.t =
    let focus, inst = Stdlib.List.split itr in
    let t = focus |> boollist_of_intlist in
    let i =
      let rec filtered_quant acc mode itr lp lf rp rf =
        begin
          match itr with
          | [] -> acc
          | ((side, _) as step) :: subitr -> (
              let p, f = if side = 0 then (lp, lf) else (rp, rf) in
              match p with
              | [] -> acc
              | i :: subp ->
                  let subf = direct_subform f i in
                  let lp, lf, rp, rf =
                    if side = 0 then (subp, subf, rp, rf) else (lp, lf, subp, subf)
                  in
                  begin
                    match (f, (mode, side, i)) with
                    | Logic.FBind (q, _, _, _), _ ->
                        let instantiable =
                          begin
                            match (mode, side, q) with
                            | `Back, 0, Logic.Forall
                            | `Back, 1, Logic.Exist
                            | `Forw, _, Logic.Forall ->
                                true
                            | _ -> false
                          end
                        in
                        if instantiable
                        then filtered_quant (acc @ [ step ]) mode subitr lp lf rp rf
                        else filtered_quant acc mode subitr lp lf rp rf
                    | Logic.FConn ((Logic.Not | Logic.Imp), _), (`Forw, _, 0 | `Back, 1, 0) ->
                        let mode, (lp, lf, rp, rf) =
                          begin
                            match mode with
                            | `Back -> (`Forw, (lp, lf, rp, rf))
                            | `Forw ->
                                (`Back, if side = 0 then (rp, rf, lp, lf) else (lp, lf, rp, rf))
                          end
                        in
                        filtered_quant acc mode subitr lp lf rp rf
                    | _ -> filtered_quant acc mode subitr lp lf rp rf
                  end)
        end
      in
      let i =
        filtered_quant [] mode itr lp lf rp rf
        |> List.map
             begin
               fun (side, w) ->
                 Option.map
                   begin
                     fun (le1, le2, e) ->
                       let lenv = if side = 0 then le2 else le1 in
                       let ty = infer_sort (Utils.Vars.push_lenv env lenv) e in
                       let s = Trm.Datatypes.of_nat coq_env (sort_index sign ty) in
                       let e =
                         let body = expr_itrace coq_env sign env lenv (1 - side) e in
                         Trm.lambda sigma "env1" (env_ty ts ())
                           (Trm.lambda sigma "env2" (env_ty ts ()) body)
                       in
                       Trm.Specif.existT coq_env sigma "s" (Trm.Datatypes.nat coq_env)
                         (clos_ty ts ()) s e
                   end
                   w
             end
      in
      Trm.Datatypes.of_list coq_env
        (Trm.Datatypes.option coq_env (inst1_ty ts ()))
        (Trm.Datatypes.of_option coq_env (inst1_ty ts ()) identity)
        i
    in
    (t, i)

  (** Make an introduction pattern to introduce named variables.
      If any of the given names is already bound, this will create a fresh name instead. *)
  let mk_intro_patterns (names : string list) : Tactypes.intro_patterns =
    let open Tactypes in
    List.map
      (fun name -> CAst.make (IntroNaming (Namegen.IntroFresh (Names.Id.of_string name))))
      names

  let bool_path coq_env (sub : int list) : EConstr.t =
    let boollist_of_intlist = Stdlib.List.map (fun n -> if n = 0 then false else true) in
    sub |> boollist_of_intlist |> Trm.Datatypes.boollist coq_env

  let fix_sub_eq (t : Logic.term) (sub : int list) : int list =
    let rec aux acc t sub =
      begin
        match sub with
        | [] -> Stdlib.List.rev acc
        | i :: sub ->
            let j =
              begin
                match t with Logic.F (Logic.FPred ("_EQ", _)) -> i + 1 | _ -> i
              end
            in
            aux (j :: acc) (Utils.direct_subterm t i) sub
      end
    in
    aux [] t sub

  exception UnsupportedAction of Logic.action
  exception UnexpectedDnD
  exception InvalidPath of Logic.ipath

  (** Contains the lemma name and an error message. *)
  exception InvalidLemma of string * string

  let mpath_to_string mpath =
    let prefix =
      match mpath with
      | Names.ModPath.MPfile _ -> "MPfile::"
      | Names.ModPath.MPbound _ -> "MPbound::"
      | Names.ModPath.MPdot _ -> "MPdot::"
    in
    prefix ^ Names.ModPath.to_string mpath

  let print_kername kname =
    let mpath = Names.KerName.modpath kname in
    let label = Names.KerName.label kname in
    Log.str @@ Format.sprintf "%s::%s" (mpath_to_string mpath) (Names.Label.to_string label)

  (** Decode a lemma name, as encoded by Export.encode_lemma_name. *)
  let decode_lemma_name (name : string) : Names.Constant.t option =
    let parse dirpath modpath label =
      let dirpath =
        (if dirpath = "" then [] else String.split_on_char '.' dirpath)
        |> List.rev_map Names.Id.of_string |> Names.DirPath.make
      in
      let modpath =
        (if modpath = "" then [] else String.split_on_char '.' modpath) |> List.map Names.Label.make
      in
      let modpath =
        List.fold_left
          begin
            fun acc label -> Names.ModPath.MPdot (acc, label)
          end
          (Names.ModPath.MPfile dirpath) modpath
      in
      let label = Names.Label.make label in
      Names.Constant.make2 modpath label
    in
    try Some (Scanf.sscanf name "C%s@/%s@/%s" parse) with _ -> None

  (** Decode a constructor name, as encoded by Export.encode_constructor_name. *)
  let decode_constructor_name (name : string) : Names.Construct.t option =
    let parse dirpath modpath label i j =
      let dirpath =
        (if dirpath = "" then [] else String.split_on_char '.' dirpath)
        |> List.rev_map Names.Id.of_string |> Names.DirPath.make
      in
      let modpath =
        (if modpath = "" then [] else String.split_on_char '.' modpath) |> List.map Names.Label.make
      in
      let modpath =
        List.fold_left
          begin
            fun acc label -> Names.ModPath.MPdot (acc, label)
          end
          (Names.ModPath.MPfile dirpath) modpath
      in
      let label = Names.Label.make label in
      let mind = Names.MutInd.make2 modpath label in
      ((mind, i), j)
    in
    try Some (Scanf.sscanf name "I%s@/%s@/%s@/%d/%d" parse) with _ -> None

  let action (sign : FOSign.t) (goal : Logic.goal) (coq_goal : Goal.t) (a : Logic.action) :
      unit tactic =
    let open PVMonad in
    match a with
    | Logic.AId -> Tacticals.tclIDTAC
    | Logic.ALemma full_name ->
        (* Decode the lemma name. *)
        let stmt, basename =
          match decode_lemma_name full_name with
          (* Case of a lemma that comes from a constant. *)
          | Some const_name ->
              (* Check the lemma exists in the environment. *)
              if not @@ Environ.mem_constant const_name (Goal.env coq_goal)
              then raise @@ InvalidLemma (full_name, "Name matches no lemma in the COQ environment.");
              (* Create a term containing the lemma. *)
              let (_, inst), _ = UnivGen.fresh_constant_instance (Goal.env coq_goal) const_name in
              let stmt = EConstr.mkConstU (const_name, EConstr.EInstance.make inst) in
              (* Choose a base name for the hypothesis. *)
              let basename = Names.Constant.label const_name |> Names.Label.to_string in
              (stmt, basename)
          | None -> begin
              match decode_constructor_name full_name with
              (* Case of a lemma that comes from an inductive constructor. *)
              | Some ((mind_name, i), j) ->
                  (* Check the mutual inductive block exists in the environment. *)
                  if not @@ Environ.mem_mind mind_name (Goal.env coq_goal)
                  then
                    raise
                    @@ InvalidLemma
                         (full_name, "Name matches no mutual inductive in the COQ environment.");
                  let mind_body = Environ.lookup_mind mind_name (Goal.env coq_goal) in
                  (* Check the inductive exists. *)
                  if i < 0 || i >= mind_body.Declarations.mind_ntypes
                  then
                    raise
                    @@ InvalidLemma
                         (full_name, Format.sprintf "Inductive index %d is out of bounds." i);
                  let ind_body = mind_body.Declarations.mind_packets.(i) in
                  (* Check the constructor exists. *)
                  if j < 1 || j > Array.length ind_body.Declarations.mind_consnames
                  then
                    raise
                    @@ InvalidLemma
                         (full_name, Format.sprintf "Constructor index %d is out of bounds." j);
                  let constr_name = ind_body.Declarations.mind_consnames.(j - 1) in
                  (* Create a term containing the lemma. *)
                  let (_, inst), _ =
                    UnivGen.fresh_constructor_instance (Goal.env coq_goal) ((mind_name, i), j)
                  in
                  let stmt =
                    EConstr.mkConstructU (((mind_name, i), j), EConstr.EInstance.make inst)
                  in
                  (* Choose a base name for the hypothesis. *)
                  let basename = Names.Id.to_string constr_name in
                  (stmt, basename)
              | None -> raise @@ InvalidLemma (full_name, "Could not decode lemma name.")
            end
        in
        (* Choose a name for the hypothesis. *)
        let hyp_name = Names.Name.mk_name @@ Goal.fresh_name ~basename coq_goal () in
        (* Add the lemma as a hypothesis. *)
        Tactics.pose_proof hyp_name stmt
    | Logic.AExact id ->
        let name = Names.Id.of_string id in
        Tactics.exact_check (EConstr.mkVar name)
    | Logic.ADef (x, _, e) ->
        let id = Names.Id.of_string x in
        let name = Names.Name.Name id in
        let body = expr sign [] e in
        Tactics.pose_tac name body
    | Logic.ACut f ->
        let id = Goal.fresh_name coq_goal () |> Names.Name.mk_name in
        let form = form (Goal.env coq_goal) (Goal.sigma coq_goal) sign goal.g_env [] f in
        Tactics.assert_before id form
    | Logic.AIntro (iv, wit) -> begin
        match goal.g_concl with
        | Logic.FTrue -> Tactics.one_constructor 1 Tactypes.NoBindings
        | Logic.FConn (Logic.Imp, _) | Logic.FConn (Logic.Not, _) ->
            let pat = mk_intro_patterns [ "imp_left" ] in
            Tactics.intro_patterns false pat
        | Logic.FConn (Logic.And, _) | Logic.FConn (Logic.Equiv, _) ->
            Tactics.split Tactypes.NoBindings
        | Logic.FConn (Logic.Or, _) as f ->
            let rec arity acc f =
              match f with Logic.FConn (Logic.Or, [ f1; f2 ]) -> arity (acc + 1) f1 | _ -> acc + 1
            in
            let rec aux zero i =
              match i with
              | 1 when zero -> Tactics.left Tactypes.NoBindings
              | 0 -> Tactics.right Tactypes.NoBindings
              | n ->
                  let* _ = Tactics.left Tactypes.NoBindings in
                  aux zero (n - 1)
            in
            aux (iv = 0) (arity 0 f - iv - 1)
        | Logic.FBind (Logic.Forall, x, _, _) ->
            let pat = mk_intro_patterns [ x ] in
            Tactics.intro_patterns false pat
        | Logic.FPred ("_EQ", _) ->
            (* Here we are not sure that the two sides of the equality are indeed equal.

               The frontend can only handle syntactic equality : it delegates to the plugin
               the responsability of dealing with non-equal terms.

               We choose to simply ignore an intro action on an equality that is not provable by computation. *)
            Tacticals.tclTRY Tactics.reflexivity
        | _ -> raise (UnsupportedAction a)
      end
    | Logic.AElim (uid, i) ->
        (* This action eliminates the hypothesis named [uid]. The hypothesis is cleared and replaced
           by (possibly several goals) which contain derived hypotheses. The integer index is used when
           eliminating an equality, to decide which way (left/right) to rewrite. *)
        let id = Names.Id.of_string uid in
        let hyp = Utils.get_hyp goal uid in
        begin
          match hyp.h_form with
          | Logic.FTrue | Logic.FFalse | Logic.FConn (Logic.Not, _) ->
              let bindings = (EConstr.mkVar id, Tactypes.NoBindings) in
              Tactics.default_elim false (Some true) bindings
          | Logic.FConn (Logic.Imp, _) -> Tactics.apply (EConstr.mkVar id)
          | Logic.FConn (Logic.And, _) | Logic.FConn (Logic.Equiv, _) ->
              (* First eliminate the hypothesis, then introduce the hypotheses we created. *)
              let bindings = (EConstr.mkVar id, Tactypes.NoBindings) in
              Tacticals.tclTHENS
                (Tactics.default_elim false (Some true) bindings)
                [ Tactics.intro_patterns false @@ mk_intro_patterns [ uid; uid ] ]
          | Logic.FConn (Logic.Or, _) ->
              (* First eliminate the hypothesis, then introduce the hypotheses we created. *)
              let bindings = (EConstr.mkVar id, Tactypes.NoBindings) in
              Tacticals.tclTHENS
                (Tactics.default_elim false (Some true) bindings)
                [ Tactics.intro_patterns false @@ mk_intro_patterns [ uid ]
                ; Tactics.intro_patterns false @@ mk_intro_patterns [ uid ]
                ]
          | Logic.FBind (Logic.Exist, x, _, _) ->
              (* First eliminate the hypothesis, then introduce the variable and hypothesis we created. *)
              let bindings = (EConstr.mkVar id, Tactypes.NoBindings) in
              Tacticals.tclTHENS
                (Tactics.default_elim false (Some true) bindings)
                [ Tactics.intro_patterns false @@ mk_intro_patterns [ x; uid ] ]
          | Logic.FPred ("_EQ", _) -> begin
              match i with
              | 0 -> calltac (kname "rew_all_left") [ EConstr.mkVar id ]
              | 1 -> calltac (kname "rew_all_right") [ EConstr.mkVar id ]
              | _ -> raise (UnsupportedAction a)
            end
          | _ -> raise (UnsupportedAction a)
        end
    | Logic.ALink (src, dst, itr) ->
        let get_eq (p : Logic.ipath) : (bool list * bool) option =
          match Stdlib.List.rev p.sub with
          | side :: rsub -> begin
              let p = { p with sub = Stdlib.List.rev rsub } in
              try
                let t = term_of_ipath goal p in
                let pol = pol_of_ipath goal p in
                begin
                  match (pol, t |> form_of_term) with
                  | Neg, Logic.FPred ("_EQ", [ _; _ ]) ->
                      let hp = p.sub |> boollist_of_intlist in
                      let bside = match side with 0 -> false | _ -> true in
                      Some (hp, bside)
                  | _ -> None
                end
              with
              (* path does not lead to a formula *)
              | Invalid_argument _ | InvalidSubFormPath _ ->
                None
            end
          | _ -> None
        in

        let get_term (p : Logic.ipath) : (bool list * int list) option =
          let rec aux fsub esub t sub =
            match sub with
            | [] -> Some (fsub, esub)
            | i :: sub -> (
                try
                  let subt = direct_subterm t i in
                  let fsub, esub =
                    begin
                      match subt with
                      | Logic.F _ -> (fsub @ [ i ], esub)
                      | Logic.E _ ->
                          (* let i =
                             begin match t with
                             | `F (Logic.FPred ("_EQ", _)) -> i + 1
                             | _ -> i
                             end in *)
                          (fsub, esub @ [ i ])
                    end
                  in
                  aux fsub esub subt sub
                with InvalidSubFormPath s | InvalidSubExprPath s -> None)
          in
          let open Monads.Option in
          let t = term_of_ipath goal { p with sub = [] } in
          let* fsub, esub = aux [] [] t p.sub in
          Some (boollist_of_intlist fsub, esub)
        in

        let rewrite_data =
          begin
            match (get_eq src, get_term dst) with
            | Some (hsub, side), Some (fsub, esub) -> Some (false, hsub, side, fsub, esub)
            | _ -> begin
                match (get_eq dst, get_term src) with
                | Some (hsub, side), Some (fsub, esub) -> Some (true, hsub, side, fsub, esub)
                | _ -> None
              end
          end
        in

        let ts = sorts (Goal.env coq_goal) sign in

        begin
          match ((src, src.ctxt.kind), (dst, dst.ctxt.kind)) with
          (* Forward DnD *)
          | (src, Logic.Hyp), (dst, Logic.Hyp) ->
              let t, i =
                let lp = src.sub in
                let rp = dst.sub in
                let lf = (Utils.get_hyp goal src.ctxt.handle).h_form in
                let rf = (Utils.get_hyp goal dst.ctxt.handle).h_form in
                itrace (Goal.env coq_goal) (Goal.sigma coq_goal) ts sign goal.g_env `Forw lp rp lf
                  rf itr
              in

              begin
                match rewrite_data with
                (* Rewrite *)
                | Some (eqside, hsub, side, fsub, esub) ->
                    let eq_hyp, dst_hyp = if eqside then (dst, src) else (src, dst) in
                    let fl = Trm.Datatypes.of_bool (Goal.env coq_goal) eqside in
                    let h1 =
                      let id = Names.Id.of_string eq_hyp.ctxt.handle in
                      EConstr.mkVar id
                    in
                    let id2 = Names.Id.of_string dst_hyp.ctxt.handle in
                    let h2 = EConstr.mkVar id2 in
                    let h3 =
                      let id = Goal.fresh_name ~basename:(Names.Id.to_string id2) coq_goal () in
                      EConstr.mkVar id
                    in

                    let t = Trm.Datatypes.boollist (Goal.env coq_goal) (t @ [ side ]) in

                    let hp1 = Trm.Datatypes.boollist (Goal.env coq_goal) hsub in
                    let hp2 = Trm.Datatypes.boollist (Goal.env coq_goal) fsub in
                    let hp2' = Trm.Datatypes.natlist (Goal.env coq_goal) esub in

                    let log t =
                      Log.econstr (Goal.env coq_goal) (Goal.sigma coq_goal) t;
                      Log.str ""
                    in
                    if log_dnd_trace
                    then begin
                      log h1;
                      log h2;
                      log h3;
                      log hp1;
                      log hp2;
                      log hp2';
                      log t;
                      log i
                    end;

                    let forw = kname "rew_dnd_hyp" in
                    calltac forw [ ts; fl; h1; h2; h3; hp1; hp2; hp2'; t; i ]
                (* Non-rewrite *)
                | None ->
                    let h1 =
                      let id = Names.Id.of_string src.ctxt.handle in
                      EConstr.mkVar id
                    in
                    let id2 = Names.Id.of_string dst.ctxt.handle in
                    let h2 = EConstr.mkVar id2 in
                    let h3 =
                      let id = Goal.fresh_name ~basename:(Names.Id.to_string id2) coq_goal () in
                      EConstr.mkVar id
                    in

                    let t = Trm.Datatypes.boollist (Goal.env coq_goal) t in

                    let hp1 = bool_path (Goal.env coq_goal) src.sub in
                    let hp2 = bool_path (Goal.env coq_goal) dst.sub in

                    let log t =
                      Log.econstr (Goal.env coq_goal) (Goal.sigma coq_goal) t;
                      Log.str ""
                    in
                    if log_dnd_trace
                    then begin
                      log h1;
                      log h2;
                      log h3;
                      log hp1;
                      log hp2;
                      log t;
                      log i
                    end;

                    let forw = kname "forward" in
                    calltac forw [ ts; h1; h2; h3; hp1; hp2; t; i ]
              end
          (* Backward DnD *)
          | (hyp, Logic.Hyp), (concl, Logic.Concl) | (concl, Logic.Concl), (hyp, Logic.Hyp) ->
              let h =
                let id = Names.Id.of_string hyp.ctxt.handle in
                EConstr.mkVar id
              in

              let t, i =
                let lp = hyp.sub in
                let rp = concl.sub in
                let lf = (Utils.get_hyp goal hyp.ctxt.handle).h_form in
                let rf = goal.g_concl in
                itrace (Goal.env coq_goal) (Goal.sigma coq_goal) ts sign goal.g_env `Back lp rp lf
                  rf itr
              in

              begin
                match rewrite_data with
                | Some (_, hsub, side, fsub, esub) ->
                    let t = Trm.Datatypes.boollist (Goal.env coq_goal) (t @ [ side ]) in

                    let hp = Trm.Datatypes.boollist (Goal.env coq_goal) hsub in
                    let gp = Trm.Datatypes.boollist (Goal.env coq_goal) fsub in
                    let gp' = Trm.Datatypes.natlist (Goal.env coq_goal) esub in

                    let log t =
                      Log.econstr (Goal.env coq_goal) (Goal.sigma coq_goal) t;
                      Log.str ""
                    in
                    if log_dnd_trace
                    then begin
                      log h;
                      log hp;
                      log gp';
                      log gp;
                      log t;
                      log i
                    end;

                    let back = kname "rew_dnd" in
                    calltac back [ ts; h; hp; gp'; gp; t; i ]
                | None ->
                    let t = Trm.Datatypes.boollist (Goal.env coq_goal) t in

                    let hp = bool_path (Goal.env coq_goal) hyp.sub in
                    let gp = bool_path (Goal.env coq_goal) concl.sub in

                    let log t =
                      Log.econstr (Goal.env coq_goal) (Goal.sigma coq_goal) t;
                      Log.str ""
                    in
                    if log_dnd_trace
                    then begin
                      log h;
                      log hp;
                      log gp;
                      log t;
                      log i
                    end;

                    let back = kname "back" in
                    calltac back [ ts; h; hp; gp; t; i ]
              end
          | _ -> raise UnexpectedDnD
        end
    | Logic.AInstantiate (wit, tgt) ->
        let l = bool_path (Goal.env coq_goal) (tgt.sub @ [ 0 ]) in
        let s =
          infer_sort goal.g_env wit |> sort_index sign |> Trm.Datatypes.of_nat (Goal.env coq_goal)
        in
        let o = expr sign [] wit in
        let ts = sorts (Goal.env coq_goal) sign in

        let tac, args =
          begin
            match tgt.ctxt.kind with
            (* Forward instantiate *)
            | Logic.Hyp ->
                let id = Names.Id.of_string tgt.ctxt.handle in
                let h = EConstr.mkVar id in
                let id' = Goal.fresh_name ~basename:(Names.Id.to_string id) coq_goal () in
                let h' = EConstr.mkVar id' in
                (kname "inst_hyp", [ ts; l; h; h'; s; o ])
            (* Backward instantiate *)
            | Logic.Concl -> (kname "inst_goal", [ ts; l; s; o ])
            | _ -> raise (InvalidPath tgt)
          end
        in

        calltac tac args
    | Logic.ADuplicate uid ->
        let id = Names.Id.of_string uid in
        let name =
          let name = Goal.fresh_name ~basename:(Names.Id.to_string id) coq_goal () in
          Names.Name.mk_name name
        in
        let prf = EConstr.mkVar id in

        Tactics.pose_proof name prf
    | Logic.ASimpl tgt | Logic.ARed tgt | Logic.AIndt tgt | Logic.ACase tgt | Logic.APbp tgt ->
        let tac_name =
          begin
            match a with
            | Logic.ASimpl _ -> "simpl_path"
            | Logic.ARed _ -> "unfold_path"
            | Logic.AIndt _ -> "myinduction"
            | Logic.APbp _ -> "pbp"
            | Logic.ACase _ -> "mycase"
            | _ -> assert false
          end
        in

        let tac_name, args =
          begin
            match tgt.ctxt.kind with
            | Logic.Hyp ->
                (* let p = tgt.sub |> fix_sub_eq (`F hyp.h_form) |> Trm.natlist in *)
                let p = tgt.sub |> Trm.Datatypes.natlist (Goal.env coq_goal) in
                let id = Names.Id.of_string tgt.ctxt.handle in
                let h = EConstr.mkVar id in
                (tac_name ^ "_hyp", [ h; p ])
            | Logic.Concl ->
                (* let p = tgt.sub |> fix_sub_eq (`F goal.g_concl) |> Trm.natlist in *)
                let p = tgt.sub |> Trm.Datatypes.natlist (Goal.env coq_goal) in
                (tac_name, [ p ])
            | _ -> raise (InvalidPath tgt)
          end
        in

        calltac (kname tac_name) args
    | _ -> raise (UnsupportedAction a)
end
