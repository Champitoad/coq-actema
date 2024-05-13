open CoqUtils
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
