open Proofview
open CoqUtils
open Utils
open Extlib

(* -------------------------------------------------------------------- *)
(** * Configuration flags *)

(** ** Debug logging *)

(** Set to true to log the arguments given to the DnD tactics *)
let log_dnd_trace = false

(** Set to true to print the atdgen-formatted goals exported to Actema *)
let log_goals = false

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
end with type t = symbol = struct
  type t = symbol

  let to_string = function
    | Cst c ->
        Names.Constant.to_string c
    | Ctr ((mind, i), j) ->
        Printf.sprintf "%s_%d_%d" (Names.MutInd.to_string mind) i j
    | Ind (mind, i) ->
        Printf.sprintf "%s_%d" (Names.MutInd.to_string mind) i
    | Var id ->
        Names.Id.to_string id

  let compare x y =
    compare (to_string x) (to_string y)
end

module NameMap = Map.Make(String)

module FOSign = struct
  module SymbolNames = BiMap(Symbol)(String)
  module SymbolMap = Map.Make(Symbol)

  type symbols = SymbolNames.t
  
  type typing =
    { t_funcs : Fo_t.sig_ NameMap.t; t_preds : Fo_t.arity NameMap.t }
  
  type t =
    { symbols : symbols; typing : typing; defaults : EConstr.t SymbolMap.t }
  
  let empty : t =
    { symbols = SymbolNames.empty;
      typing = {
        t_funcs = NameMap.empty;
        t_preds = NameMap.empty; };
      defaults = SymbolMap.empty; }
  
  let union (s1 : t) (s2 : t) : t =
    let f _ x _ = Some x in
    { symbols = SymbolNames.union s1.symbols s2.symbols;
      typing = {
        t_funcs = NameMap.union f s1.typing.t_funcs s2.typing.t_funcs;
        t_preds = NameMap.union f s1.typing.t_preds s2.typing.t_preds; };
      defaults = SymbolMap.union f s1.defaults s2.defaults; }
  
  let sort_symbols (sign : t) : SymbolNames.t =
    sign.symbols |> 
    SymbolNames.filter begin fun _ n ->
      not (NameMap.mem n sign.typing.t_funcs
        || NameMap.mem n sign.typing.t_preds)
    end
    
  let sort_names (sign : t) : string list =
    sign |> sort_symbols |> SymbolNames.values
end

let peano : FOSign.t =
  let open FOSign in
  let open Trm in
  let nat : Fo_t.type_ = `TVar "nat" in
  let symbols =
    let open SymbolNames in
    empty |>
    add (Ind nat_name) "nat" |>
    add (Ctr zero_name) "Z" |>
    add (Ctr succ_name) "S" |> fun m ->
    List.fold_left (fun m name -> add (Cst name) "add" m) m Trm.add_names |> fun m ->
    List.fold_left (fun m name -> add (Cst name) "mult" m) m Trm.mul_names in
  let typing =
    let open NameMap in
    let t_funcs = empty |>
      add "Z" ([], nat) |>
      add "S" ([nat], nat) |>
      add "add" ([nat; nat], nat) |>
      add "mult" ([nat; nat], nat) in
    let t_preds = empty in
    { t_funcs; t_preds } in
  let defaults =
    let open SymbolMap in
    empty |>
    add (Ind nat_name) zero in
  { symbols; typing; defaults }

(* -------------------------------------------------------------------- *)
(** * Exporting Coq goals to Actema *)

module Export = struct
  (** ** Translating Coq terms to Actema expressions and formulas *)

  let dummy_expr : Logic_t.expr =
    `EFun ("_dummy", [])

  let dummy_form : Logic_t.form =
    `FPred ("_dummy", [])

  let is_prop env evd term =
    let sort = Retyping.get_sort_of env evd term in
    Sorts.is_prop sort

  let is_imp (env, evd) x t1 t2 : bool = 
    is_prop env evd t1
    && is_prop
        (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (x, t1)) env)
        evd t2
    && (x.Context.binder_name = Names.Anonymous || EConstr.Vars.noccurn evd 1 t2)

  type destenv =
    { env : Environ.env; evd : Evd.evar_map }
  
  type destarg = destenv * EConstr.types

  module State = Monads.State(FOSign)
  module Dest = Monads.StateOption(FOSign)

  type 'a sdest = destarg -> 'a Dest.t

  let state_to_dest (m : 'a State.t) : 'a Dest.t =
    fun sign ->
      let res, sign = State.run m sign in
      Some (res, sign)

  let dest_to_state default (m : 'a Dest.t) : 'a State.t =
    fun sign ->
      match Dest.run m sign with
      | None -> (default, sign)
      | Some (v, sign) -> (v, sign)

  open FOSign
  open Dest

  let destKO = lift None

  let destwrap (f : 'a -> 'b) (x : 'a) : 'b Dest.t =
    try return (f x)
    with Constr.DestKO -> destKO

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

  let rec dest_sort ({ evd; _ }, t : destarg) : unit Dest.t =
    let* sort = destwrap (EConstr.destSort evd) t in
    let sort = EConstr.ESorts.kind evd sort in
    if sort <> Sorts.set && sort <> Sorts.type1
    then destKO
    else return ()

  and dest_functy ({ evd; _ } as e, t : destarg) : Fo_t.sig_ Dest.t =
    let rec aux arity t =
      if EConstr.isProd evd t then
        let* _, t1, t2 = destwrap (EConstr.destProd evd) t in
        let* sort = find_sort (e, t1) in
        aux (arity @ [`TVar sort]) t2
      else
        let* sort = find_sort (e, t) in
        return (arity, `TVar sort) in
    aux [] t

  and dest_predty ({ evd; _ } as e, t : destarg) : Fo_t.arity Dest.t =
    let rec aux arity t =
      if EConstr.isProd evd t then
        let* _, t1, t2 = destwrap (EConstr.destProd evd) t in
        let* sort = find_sort (e, t1) in
        aux (arity @ [`TVar sort]) t2
      else
        let* sort = t |> EConstr.to_constr evd |> destwrap Constr.destSort in
        if Sorts.is_prop sort then
          return arity
        else
          destKO in
    aux [] t

  and add_sort name sy ty (e : destenv) : unit Dest.t =
    let* () = dest_sort (e, ty) in
    let* sign = get in
    let symbols = SymbolNames.add sy name sign.symbols in
    put { sign with symbols }

  and add_func ?(strict = false) name sy ty (e : destenv) : unit Dest.t =
    let* sig_ = dest_functy (e, ty) in
    if strict && List.length (fst sig_) = 0 then destKO else
    let* sign = get in
    let symbols = SymbolNames.add sy name sign.symbols in
    let t_funcs = NameMap.add name sig_ sign.typing.t_funcs in
    let typing = { sign.typing with t_funcs } in
    put { sign with symbols; typing }

  and add_pred name sy ty (e : destenv) : unit Dest.t =
    let* arity = dest_predty (e, ty) in
    let* sign = get in
    let symbols = SymbolNames.add sy name sign.symbols in
    let t_preds = NameMap.add name arity sign.typing.t_preds in
    let typing = { sign.typing with t_preds } in
    put { sign with symbols; typing }

  and add_default t ty (e : destenv) : unit Dest.t =
    let* sort_sy = dest_symbol (e, ty) in
    let* sign = get in
    if SymbolMap.mem sort_sy sign.defaults then destKO else
    put { sign with defaults = SymbolMap.add sort_sy t sign.defaults }
  
  and add_symbol ?(strict = false) name sy ty e : unit Dest.t =
    begin
      add_sort name sy ty @>
      add_func ~strict name sy ty @>
      add_pred name sy ty @>
      fun _ -> return ()
    end e
  
  and add_symbol_lazy ?(strict = false) sy (info : unit -> string * EConstr.t) e : unit Dest.t =
    let* sign = get in
    if not (SymbolNames.mem sy sign.symbols) then
      let name, ty = info () in
      add_symbol ~strict name sy ty e
    else
      return ()

  and find_sort (d : destarg) : string Dest.t =
    let* sy = dest_symbol d in
    let* sign = get in
    match SymbolNames.find_opt sy (sort_symbols sign) with
    | Some name -> return name
    | None -> destKO

  and find_func (d : destarg) : (Fo_t.name * Fo_t.sig_) Dest.t =
    let* sy = dest_symbol d in
    let* sign = get in
    match SymbolNames.find_opt sy sign.symbols with
    | Some name ->
        let arity = NameMap.find name sign.typing.t_funcs in
        return (name, arity)
    | None -> destKO

  and find_pred (d : destarg) : (Fo_t.name * Fo_t.arity) Dest.t =
    let* sy = dest_symbol d in
    let* sign = get in
    match SymbolNames.find_opt sy sign.symbols with
    | Some name ->
        let arity = NameMap.find name sign.typing.t_preds in
        return (name, arity)
    | None -> destKO

  and dest_sconst : symbol sdest = fun ({ env; evd } as e, t) ->
    let* cst, _ = destwrap (EConstr.destConst evd) t in
    let sy = Cst cst in
    let* () =
      let info () =
        let name = Names.Constant.to_string cst in
        let c = Environ.lookup_constant cst env in
        let ty = c.const_type |> EConstr.of_constr in
        name, ty in
      add_symbol_lazy sy info e in
    return sy

  and dest_sconstruct : symbol sdest = fun ({ env; evd } as e, t) ->
    let* ctr, _ = destwrap (EConstr.destConstruct evd) t in
    let sy = Ctr ctr in
    let* () =
      let info () =
        let name = kname_of_constructor env ctr |> Names.KerName.to_string in
        let ty = type_of_constructor env ctr in
        name, ty in
      add_symbol_lazy sy info e in
    return sy
  
  and dest_sind : symbol sdest = fun ({ env; evd } as e, t) ->
    let* ind, _ = destwrap (EConstr.destInd evd) t in
    let sy = Ind ind in
    let* () =
      let info () =
        let name = kname_of_inductive env ind |> Names.KerName.to_string in
        let ty = arity_of_inductive env ind in
        name, ty in
      add_symbol_lazy sy info e in
    return sy
  
  and dest_svar : symbol sdest = fun ({ env; evd } as e, t) ->
    let* id = destwrap (EConstr.destVar evd) t in
    let sy = Var id in
    let* () =
      let info () =
        let name = Names.Id.to_string id in
        let ty =
          Environ.lookup_named id env |>
          Context.Named.Declaration.get_type |>
          EConstr.of_constr in
        name, ty in
      add_symbol_lazy ~strict:true sy info e in
    return sy

  and dest_symbol : symbol sdest = fun et ->
    begin
      dest_sconst @>
      dest_sconstruct @>
      dest_sind @>
      dest_svar
    end et
  
  type edest = Logic_t.expr sdest 

  let rec dest_econst : edest = fun (e, t) ->
    let* name, sig_ = find_func (e, t) in
    match sig_ with
    | ([], _) -> return (`EFun (name, []))
    | _ -> destKO
  
  and dest_evar : edest = fun ({ env; evd; _ }, t) ->
    let* id = destwrap (EConstr.destVar evd) t in 
    let name = Names.Id.to_string id in
    return (`EVar name)

  and dest_erel : edest = fun ({ env; evd; _ }, t) ->
    let* n = destwrap (EConstr.destRel evd) t in
    let name =
      EConstr.lookup_rel n env |>
      EConstr.to_rel_decl evd |>
      Context.Rel.Declaration.get_name in
    match name with
    | Name id -> return (`EVar (Names.Id.to_string id))
    | _ -> destKO

  and dest_eapp : edest = fun ({ evd; _ } as e, t) ->
    let* head, args = destwrap (EConstr.destApp evd) t in
    let* name, _ = find_func (e, head) in
    let* targs =
      args |> Array.to_list |>
      State.map (fun u -> dest_expr (e, u)) |>
      state_to_dest in
    return (`EFun (name, targs))
  
  and dest_edummy : destarg -> Logic_t.expr State.t = fun ({ env; evd; _ }, t) ->
    Log.str (Printf.sprintf "Failed to translate expression:\n%s"
              (Log.string_of_econstr env evd t));
    State.return dummy_expr

  and dest_expr : destarg -> Logic_t.expr State.t = fun et ->
    begin
      dest_econst @>?
      dest_evar @>?
      dest_erel @>?
      dest_eapp @>?
      dest_edummy
    end et


  type fdest = Logic_t.form sdest

  let rec dest_pconst : fdest = fun ({ env; evd; _ } as e, t) ->
    if not (is_prop env evd t) then destKO else
    let* name, _ = find_pred (e, t) in
    return (`FPred (name, []))

  and dest_pvar : fdest = fun ({ env; evd; _ }, t) ->
    if not (is_prop env evd t) then destKO else
    let* id = destwrap (EConstr.destVar evd) t in
    let name = Names.Id.to_string id in
    return (`FPred (name, []))

  and dest_papp : fdest = fun ({ env; evd; _ } as e, t) ->
    if not (is_prop env evd t) then destKO else
    let* head, args = destwrap (EConstr.destApp evd) t in
    let* name, _ = find_pred (e, head) in
    let* targs =
      args |> Array.to_list |>
      State.map (fun u -> dest_expr (e, u)) |>
      state_to_dest in
    Dest.return (`FPred (name, targs))

  and dest_eq : fdest = fun ({ env; evd; _ } as e, t) ->
    let* head, args = destwrap (EConstr.destApp evd) t in
    let* ind, _ = destwrap (EConstr.destInd evd) head in
    match Trm.Logic.eq_ind ind "eq", args with
    | true, [| _; t1; t2 |] ->
        let* e1 = dest_expr (e, t1) |> state_to_dest in
        let* e2 = dest_expr (e, t2) |> state_to_dest in
        return (`FPred ("_EQ", [e1; e2]))
    | _ ->
        destKO

  and dest_true : fdest = fun ({ env; evd; _ }, t) ->
    let* ind, _ = destwrap (EConstr.destInd evd) t in
    if Trm.Logic.eq_ind ind "True"
    then return `FTrue
    else destKO

  and dest_false : fdest = fun ({ env; evd; _ }, t) ->
    let* ind, _ = destwrap (EConstr.destInd evd) t in
    if Trm.Logic.eq_ind ind "False"
    then return `FFalse
    else destKO

  and dest_imp : fdest = fun ({ env; evd; _ } as e, t) ->
    let* x, t1, t2 = destwrap (EConstr.destProd evd) t in
    if not (is_imp (env, evd) x t1 t2) then destKO else
    let env =
      (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (x, t1)) env) in
    let* f1 = dest_form (e, t1) |> state_to_dest in
    let* f2 = dest_form ({ e with env }, t2) |> state_to_dest in
    return (`FConn (`Imp, [f1; f2]))

  and dest_and : fdest = fun ({ env; evd; _ } as e, t) ->
    let* head, args = destwrap (EConstr.destApp evd) t in
    let* ind, _ = destwrap (EConstr.destInd evd) head in
    match Trm.Logic.eq_ind ind "and", args with
    | true, [| t1; t2 |] ->
        let* f1 = dest_form (e, t1) |> state_to_dest in
        let* f2 = dest_form (e, t2) |> state_to_dest in
        return (`FConn (`And, [f1; f2]))
    | _ ->
        destKO

  and dest_or : fdest = fun ({ env; evd; _ } as e, t) ->
    let* head, args = destwrap (EConstr.destApp evd) t in
    let* ind, _ = destwrap (EConstr.destInd evd) head in
    match Trm.Logic.eq_ind ind "or", args with
    | true, [| t1; t2 |] ->
        let* f1 = dest_form (e, t1) |> state_to_dest in
        let* f2 = dest_form (e, t2) |> state_to_dest in
        return (`FConn (`Or, [f1; f2]))
    | _ ->
        destKO

  and dest_iff : fdest = fun ({ evd; _ } as e, t) ->
    let* head, args = destwrap (EConstr.destApp evd) t in
    let* sy = dest_sconst (e, head) in
    match sy with
    | Cst cst ->
        let not_cst = Names.Constant.make1 (Trm.Logic.kname "iff") in
        begin match Names.eq_constant_key cst not_cst, args with
        | true, [| t1; t2 |] ->
            let* f1 = dest_form (e, t1) |> state_to_dest in
            let* f2 = dest_form (e, t2) |> state_to_dest in
            return (`FConn (`Equiv, [f1; f2]))
        | _ ->
            destKO
        end
    | _ -> destKO

  and dest_not : fdest = fun ({ evd; _ } as e, t) ->
    let* head, args = destwrap (EConstr.destApp evd) t in
    let* sy = dest_sconst (e, head) in
    match sy with
    | Cst cst ->
        let not_cst = Names.Constant.make1 (Trm.Logic.kname "not") in
        begin match Names.eq_constant_key cst not_cst, args with
        | true, [| t1 |] ->
            let* f1 = dest_form (e, t1) |> state_to_dest in
            return (`FConn (`Not, [f1]))
        | _ ->
            destKO
        end
    | _ -> destKO
  
  and dest_forall : fdest = fun ({ env; evd; _ } as e, t) ->
    let* x, t1, t2 = destwrap (EConstr.destProd evd) t in
    let* sort = find_sort (e, t1) in
    match Context.binder_name x with
    | Name id ->
        let name = Names.Id.to_string id in 
        let ty = `TVar sort in
        let env =
          (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (x, t1)) env) in
        let* body = dest_form ({ e with env }, t2) |> state_to_dest in
        return (`FBind (`Forall, name, ty, body))
    | _ -> destKO
  
  and dest_exists : fdest = fun ({ env; evd; _ } as e, t) ->
    let* head, args = destwrap (EConstr.destApp evd) t in
    let* ind, _ = destwrap (EConstr.destInd evd) head in
    match Trm.Logic.eq_ind ind "ex", args with
    | true, [| _; t2 |] ->
        let* x, t1, t2 = destwrap (EConstr.destLambda evd) t2 in
        let* sort = find_sort (e, t1) in
        begin match Context.binder_name x with
        | Name id ->
            let name = Names.Id.to_string id in
            let ty = `TVar sort in
            let env =
              (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (x, t1)) env) in
            let* body = dest_form ({ e with env }, t2) |> state_to_dest in
            return (`FBind (`Exist, name, ty, body))
        | _ -> destKO
        end
    | _ -> destKO

  
  and dest_dummy : destarg -> Logic_t.form State.t = fun ({ env; evd; _ }, t) ->
    Log.str (Printf.sprintf "Failed to translate formula:\n%s"
              (Log.string_of_econstr env evd t));
    State.return dummy_form
  
  and dest_form : destarg -> Logic_t.form State.t = fun et ->
    begin
      dest_imp @>?
      dest_forall @>?
      dest_eq @>?
      dest_exists @>?
      dest_and @>?
      dest_or @>?
      dest_iff @>?
      dest_not @>?
      dest_true @>?
      dest_false @>?
      dest_papp @>?
      dest_pconst @>?
      dest_pvar @>?
      dest_dummy
    end et

  (** ** Translating Coq's global and local environments to an Actema environment *)

  open FOSign

  (* Local environment of Actema definitions *)
  type varenv = Logic_t.bvar NameMap.t
  type varsign = varenv * FOSign.t

  let shortname (fullname : string) : string =
    fullname |> String.split_on_char '.' |> List.rev |> List.hd

  let env_of_varsign (venv, sign : varsign) : Logic_t.env =
    let open FOSign in

    let env_sort =
      "_dummy" :: sort_names sign in
    let env_sort_name =
      List.(combine env_sort (map shortname env_sort)) in

    let func_names =
      sign.typing.t_funcs |> NameMap.bindings |> List.split |> fst in
    let env_fun =
      ("_dummy", ([], `TVar "_dummy")) ::
      List.map (fun f -> f, NameMap.find f sign.typing.t_funcs) func_names in
    let env_fun_name =
      List.(combine func_names (map shortname func_names)) in

    let pred_names =
      sign.typing.t_preds |> NameMap.bindings |> List.split |> fst in
    let env_prp =
      ("_dummy", []) ::
      List.map (fun p -> p, NameMap.find p sign.typing.t_preds) pred_names in
    let env_prp_name =
      List.(combine pred_names (map shortname pred_names)) in

    let env_var = NameMap.bindings venv in

    { env_sort; env_sort_name;
      env_fun; env_fun_name;
      env_prp; env_prp_name;
      env_var }

  let add_var name ty value ({ env; evd} as e : destenv) (venv : varenv) : varenv Dest.t =
    let* sort = find_sort (e, ty) in
    let* body =
      match value with
      | None -> return None
      | Some v ->
          let* body = dest_expr (e, EConstr.of_constr v) |> state_to_dest in
          return (Some body) in
    return (NameMap.add name (`TVar sort, body) venv)

  let local_env ({ env = coq_env; _ } as e : destenv) : varenv State.t = 
    (* Add sorts, default elements, functions, predicates and variables defined
       as local variables *)
    State.fold begin fun venv decl ->
        let id = Context.Named.Declaration.get_id decl in
        let name = id |> Names.Id.to_string in
        let ty = decl |> Context.Named.Declaration.get_type |> EConstr.of_constr in
        let value = Context.Named.Declaration.get_value decl in

        let open State in

        let* () = begin
            add_sort name (Var id) ty @>?
            add_default (EConstr.mkVar id) ty @>?
            add_func ~strict:true name (Var id) ty @>?
            add_pred name (Var id) ty @>?
            fun _ -> return ()
          end e in
        
        let* venv = begin
            add_var name ty value e @>?
            return
          end venv in

        return venv
      end NameMap.empty (Environ.named_context coq_env)

  let hyps ({ env = coq_env; evd; _ } as e : destenv) : Logic_t.hyp list State.t =
    State.fold begin fun hyps decl ->
      let name = Context.Named.Declaration.get_id decl in
      let ty = decl |> Context.Named.Declaration.get_type |> EConstr.of_constr in
      dest_to_state hyps begin
        let open Dest in
        if is_prop coq_env evd ty then
          let h_id = Names.Id.to_string name in
          let* h_form = dest_form (e, ty) |> state_to_dest in
          let hyp = Logic_t.{ h_id; h_form } in
          return (hyps @ [hyp])
        else
          return hyps
      end
    end [] (Environ.named_context coq_env)

  (* [goal env sign gl] exports the Coq goal [gl] into an Actema goal and a
     mapping from Actema uids to Coq identifiers *)
  let goal (goal : Goal.t) : Logic_t.goal * FOSign.t =
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
      
      return Logic_t.{ g_env; g_hyps; g_concl } in

    let goal, sign = run goal peano in
    if log_goals then begin
      (* Log.str (List.to_string (fun (f, _) -> f) goal.g_env.env_fun); *)
      (* Log.str (Utils.string_of_form goal.g_concl); *)
      Log.str (Utils.string_of_goal goal);
    end;
    goal, sign
end

(* -------------------------------------------------------------------- *)
(** * Importing Actema actions as Coq tactics *)

module Import = struct
  (* let kname = kername ["Actema"; "DnD"] *)
  let kname = kername ["Actema"; "HOL"]

  let symbol (sy : symbol) : EConstr.t =
    match sy with
    | Cst c -> EConstr.mkConst c
    | Ctr c -> EConstr.mkConstruct c
    | Ind i -> EConstr.mkInd i
    | Var x -> EConstr.mkVar x
  
  let sort_index (sign : FOSign.t) (s : string) : int =
    let sorts =
      sign.defaults |> FOSign.SymbolMap.bindings |>
      List.split |> fst |>
      List.map (fun sy -> FOSign.SymbolNames.find sy sign.symbols) in
    List.nth_index 0 s sorts
  
  let infer_sort (env : Logic_t.env) (e : Logic_t.expr) : string =
    match einfer env e with
    | `TVar name -> name
    
  let nth_sort (sign : FOSign.t) (n : int) : EConstr.t =
    let sorts = FOSign.(sort_symbols sign |> SymbolNames.keys) in
    match List.nth_opt sorts n with
    | None -> Trm.unit
    | Some sy -> symbol sy

  let dyn_ty () : EConstr.t =
    EConstr.mkInd (Names.MutInd.make1 (kname "DYN"), 0)
  
  let mdyn sort default =
    let open EConstr in
    let mdyn = mkConstruct ((Names.MutInd.make1 (kname "DYN"), 0), 1) in
    mkApp (mdyn, [| sort; default |])
  
  let sorts (sign : FOSign.t) : EConstr.t =
    FOSign.SymbolMap.bindings sign.defaults |>
    List.map begin fun (sort_sy, default) ->
      let sort = symbol sort_sy in
      mdyn sort default
    end |>
    Trm.of_list (dyn_ty ()) identity

  let sort_ty ts (s : EConstr.t) : EConstr.t =
    let name = Names.Constant.make1 (kname "sort") in
    let ty = EConstr.mkConst name in
    EConstr.mkApp (ty, [| ts; s |])

  let env_ty ts () : EConstr.t =
    let name = Names.Constant.make1 (kname "env") in
    let ty = EConstr.mkConst name in
    EConstr.mkApp (ty, [| ts |])
  
  let clos_ty ts () : EConstr.t =
    let open EConstr in
    let sort_s = sort_ty ts (Trm.var "s") in
    mkArrowR (env_ty ts ()) (mkArrowR (env_ty ts ()) sort_s)
  
  let inst1_ty ts () : EConstr.t =
    let name = Names.Constant.make1 (kname "inst1") in
    let ty = EConstr.mkConst name in
    EConstr.mkApp (ty, [| ts |])
  
  let rec type_ (sign : FOSign.t)
      (ty : Fo_t.type_) : EConstr.t =
    match ty with
    | `TVar x ->
        symbol (FOSign.SymbolNames.dnif x sign.symbols)
  
  let rec expr (sign : FOSign.t) (lenv : Logic_t.lenv)
      (e : Fo_t.expr) : EConstr.t =
    match e with
    | `EVar x ->
        if LEnv.exists lenv x then begin
          let index : int =
            List.(lenv |> split |> fst |> nth_index 0 x) in
          EConstr.mkRel (index + 1)
        end else
          Trm.var x
    | `EFun (f, args) ->
        let head = symbol (FOSign.SymbolNames.dnif f sign.symbols) in
        let args = List.map (expr sign lenv) args in
        EConstr.mkApp (head, Array.of_list args)

  let rec expr_itrace (sign : FOSign.t)
      (env : Logic_t.env) (lenv : Logic_t.lenv) (side : int)
      (e : Fo_t.expr) : EConstr.t =
    match e with
    | `EVar x ->
        if LEnv.exists lenv x then begin
          let s = sort_index sign (infer_sort (Utils.Vars.push_lenv env lenv) e) in
          let index : int =
            List.(lenv |> split |> fst |> nth_index 0 x) in
          let env_index = if side = 0 then 2 else 1 in
          EConstr.(mkApp (mkRel env_index, Trm.[| nat_of_int s; nat_of_int index |]))
        end else
          Trm.var x
    | `EFun (f, args) ->
        let head = symbol (FOSign.SymbolNames.dnif f sign.symbols) in
        let args = List.map (expr_itrace sign env lenv side) args in
        EConstr.mkApp (head, Array.of_list args)
  
  let rec form (sign : FOSign.t)
      (env : Logic_t.env) (lenv : Logic_t.lenv)
      (f : Fo_t.form) : EConstr.t =
    let form = form sign env in
    match f with
    | `FPred ("_EQ", [t1; t2]) ->
        let ty =
          einfer (Vars.push_lenv env lenv) t1 |>
          type_ sign in
        let t1 = expr sign lenv t1 in
        let t2 = expr sign lenv t2 in
        EConstr.mkApp (Trm.Logic.eq ty, [|t1; t2|])
    | `FPred (p, args) ->
        let head = symbol (FOSign.SymbolNames.dnif p sign.symbols) in
        let args = List.map (expr sign lenv) args in
        EConstr.mkApp (head, Array.of_list args)
    | `FTrue ->
        Trm.Logic.true_
    | `FFalse ->
        Trm.Logic.false_
    | `FConn (`And, [f1; f2]) ->
        Trm.Logic.and_ (form lenv f1) (form lenv f2)
    | `FConn (`Or, [f1; f2]) ->
        Trm.Logic.or_ (form lenv f1) (form lenv f2)
    | `FConn (`Imp, [f1; f2]) ->
        Trm.Logic.imp (form lenv f1) (form lenv f2)
    | `FConn (`Equiv, [f1; f2]) ->
        Trm.Logic.iff (form lenv f1) (form lenv f2)
    | `FConn (`Not, [f1]) ->
        Trm.Logic.not (form lenv f1)
    | `FBind (`Forall, x, typ, body) ->
        let ty = type_ sign typ in
        let lenv = LEnv.enter lenv x typ in
        Trm.Logic.fa x ty (form lenv body)
    | `FBind (`Exist, x, typ, body) ->
        let ty = type_ sign typ in
        let lenv = LEnv.enter lenv x typ in
        Trm.Logic.ex x ty (form lenv body)
    | _ ->
        failwith "Unsupported formula"

  let boollist_of_intlist =
    Stdlib.List.map (fun n -> if n = 0 then false else true)

  let itrace ts (sign : FOSign.t) (env : Fo_t.env)
      (mode : [`Back | `Forw]) (lp : int list) (rp : int list)
      (lf : Logic_t.form) (rf : Logic_t.form)
      (itr : Logic_t.itrace) : bool list * EConstr.t =
    let focus, inst = Stdlib.List.split itr in
    let t = focus |> boollist_of_intlist in
    let i =
      let open EConstr in
      let open Trm in
      let rec filtered_quant acc mode itr lp lf rp rf =
        begin match itr with
        | [] -> acc
        | (side, _) as step :: subitr ->
            let p, f = if side = 0 then lp, lf else rp, rf in
            match p with [] -> acc | i :: subp ->
            let subf = direct_subform f i in
            let lp, lf, rp, rf =
              if side = 0
              then subp, subf, rp, rf
              else lp, lf, subp, subf in
            begin match f, (mode, side, i) with
            | `FBind (q, _, _, _), _ ->
                let instantiable =
                  begin match mode, side, q with
                  | `Back, 0, `Forall
                  | `Back, 1, `Exist
                  | `Forw, _, `Forall -> true
                  | _ -> false
                  end in
                if instantiable then
                  filtered_quant (acc @ [step]) mode subitr lp lf rp rf
                else
                  filtered_quant acc mode subitr lp lf rp rf
            | `FConn ((`Not | `Imp), _), ((`Forw, _, 0) | (`Back, 1, 0)) ->
                let mode, (lp, lf, rp, rf) =
                  begin match mode with
                  | `Back -> `Forw, (lp, lf, rp, rf)
                  | `Forw -> `Back,
                      (if side = 0
                       then (rp, rf, lp, lf)
                       else (lp, lf, rp, rf))
                  end in
                filtered_quant acc mode subitr lp lf rp rf
            | _ ->
                filtered_quant acc mode subitr lp lf rp rf
            end
        end in
      let i =
        filtered_quant [] mode itr lp lf rp rf |>
        List.map begin fun (side, w) ->
          Option.map begin fun (le1, le2, e) ->
            let lenv = if side = 0 then le2 else le1 in
            let ty = infer_sort (Utils.Vars.push_lenv env lenv) e in
            let s = nat_of_int (sort_index sign ty) in
            let e =
              let body = expr_itrace sign env lenv (1 - side) e in
              lambda "env1" (env_ty ts ()) (lambda "env2" (env_ty ts ()) body) in
            existT "s" nat (clos_ty ts ()) s e
          end w
        end in
      of_list (option (inst1_ty ts ())) (of_option (inst1_ty ts ()) identity) i in
    t, i

  let mk_or_and_intro_pattern (pat : Names.variable list list) : Tactypes.or_and_intro_pattern =
    let open Tactypes in
    let disj_conj =
      pat |> List.map begin fun conj ->
        conj |> List.map begin fun name ->
          CAst.make (IntroNaming (Namegen.IntroIdentifier name))
        end
      end in
    CAst.make (IntroOrPattern disj_conj)

  let mk_intro_patterns (names : Names.variable list) : Tactypes.intro_patterns =
    let open Tactypes in
    List.map (fun name -> CAst.make (IntroNaming (Namegen.IntroIdentifier name))) names
  
  let bool_path (sub : int list) : EConstr.t =
    let boollist_of_intlist =
      Stdlib.List.map (fun n -> if n = 0 then false else true) in
    sub |> boollist_of_intlist |> Trm.boollist
  
  let fix_sub_eq (t : Logic_t.term) (sub : int list) : int list =
    let rec aux acc t sub =
      begin match sub with
      | [] -> Stdlib.List.rev acc
      | i :: sub ->
          let j =
            begin match t with
            | `F `FPred ("_EQ", _) -> i + 1
            | _ -> i
            end in
          aux (j :: acc) (Utils.direct_subterm t i) sub
      end in
    aux [] t sub

  exception UnsupportedAction of Logic_t.action
  exception UnexpectedDnD
  exception InvalidPath of Logic_t.ipath

  let action (sign : FOSign.t) (goal : Logic_t.goal) (coq_goal : Goal.t)
             (a : Logic_t.action) : unit tactic =
    let open PVMonad in
    match a with
    | `AId ->
        Tacticals.tclIDTAC

    | `AExact id ->
        let name = Names.Id.of_string id in
        Tactics.exact_check (EConstr.mkVar name)

    | `ADef (x, _, e) ->
        let id = Names.Id.of_string x in
        let name = Names.Name.Name id in
        let body = expr sign [] e in
        Tactics.pose_tac name body

    | `ACut f ->
        let id = Goal.fresh_name coq_goal () |> Names.Name.mk_name in
        let form = form sign goal.g_env [] f in
        Tactics.assert_before id form

    | `AIntro (iv, wit) ->
        begin match goal.g_concl with
        | `FTrue ->
            Tactics.one_constructor 1 Tactypes.NoBindings
        | `FConn (`Imp, _) | `FConn (`Not, _) ->
            (* Generate fresh Coq identifier for intro *)
            let id = Goal.fresh_name coq_goal () in
            (* Apply intro *)
            let pat = mk_intro_patterns [id] in
            Tactics.intro_patterns false pat
        | `FConn (`And, _) | `FConn (`Equiv, _) ->
            Tactics.split Tactypes.NoBindings
        | `FConn (`Or, _) as f ->
            let rec arity acc f =
              match f with
              | `FConn (`Or, [f1; f2]) -> arity (acc + 1) f1
              | _ -> acc + 1
            in
            let rec aux zero i =
              match i with
              | 1 when zero -> Tactics.left Tactypes.NoBindings
              | 0 -> Tactics.right Tactypes.NoBindings
              | n ->
                  let* _ = Tactics.left Tactypes.NoBindings in
                  aux zero (n-1)
            in
            aux (iv = 0) (arity 0 f - iv - 1)
        | `FBind (`Forall, x, _, _) ->
            let id = Goal.fresh_name ~basename:x coq_goal () in
            let pat = mk_intro_patterns [id] in
            Tactics.intro_patterns false pat
        | `FPred ("_EQ", _) ->
            Tactics.reflexivity
        | _ ->
            raise (UnsupportedAction a)
        end

    | `AElim uid ->
        let id = Names.Id.of_string uid in
        let hyp = Utils.get_hyp goal uid in
        let mk_destruct
            (ids : Names.variable list)
            (mk_pat : Names.variable list -> Names.variable list list)
            : unit tactic =
          (* Apply destruct *)
          let h = EConstr.mkVar id in
          let pat = mk_or_and_intro_pattern (mk_pat ids) in
          Tactics.destruct false None h (Some pat) None
        in
        let destruct_and =
          let hyps_ids = Goal.hyps_names coq_goal in
          let id1 = Namegen.next_ident_away id hyps_ids in
          let id2 = Namegen.next_ident_away id (Names.Id.Set.add id1 hyps_ids) in
          let mk_ipat = function [x; y] -> [[x; y]] | _ -> assert false in
          mk_destruct [id1; id2] mk_ipat
        in
        let destruct_ex x =
          let idx = Goal.fresh_name ~basename:x coq_goal () in
          let mk_ipat = function [x; y] -> [[x; y]] | _ -> assert false in
          mk_destruct [idx; id] mk_ipat in
        let destruct_or =
          let mk_ipat = function [x; y] -> [[x]; [y]] | _ -> assert false in
          mk_destruct [id; id] mk_ipat
        in
        begin match hyp.h_form with
        | `FTrue | `FFalse ->
            Tactics.destruct false None (EConstr.mkVar id) None None
        | `FConn (`Not, _) ->
            Tactics.simplest_case (EConstr.mkVar id)
        | `FConn (`Imp, _) ->
            Tactics.apply (EConstr.mkVar id)
        | `FConn (`And, _) | `FConn (`Equiv, _) ->
            destruct_and
        | `FConn (`Or, _) ->
            destruct_or
        | `FBind (`Exist, x, _, _) ->
            destruct_ex x
        | _ ->
            raise (UnsupportedAction a)
        end

    | `ALink (src, dst, itr) ->
        let get_eq (p : Logic_t.ipath) : (bool list * bool) option =
          match Stdlib.List.rev p.sub with
          | side :: rsub ->
              begin
                let p = { p with sub = Stdlib.List.rev rsub } in
                try
                  let t = term_of_ipath goal p in
                  let pol = pol_of_ipath goal p in
                  begin match pol, t |> form_of_term with
                  | Neg, `FPred ("_EQ", [_; _]) ->
                      let hp = p.sub |> boollist_of_intlist in
                      let bside = match side with 0 -> false | _ -> true in
                      Some (hp, bside)
                  | _ ->
                      None
                  end
                with
                (* path does not lead to a formula *)
                | Invalid_argument _
                | InvalidSubFormPath _ -> None
              end
          | _ -> None in

        let get_term (p : Logic_t.ipath) : (bool list * int list) option =
          let rec aux fsub esub t sub =
            match sub with
            | [] -> Some (fsub, esub)
            | i :: sub ->
                try
                  let subt = direct_subterm t i in
                  let fsub, esub =
                    begin match subt with
                    | `F _ ->
                        fsub @ [i], esub
                    | `E _ ->
                        (* let i =
                          begin match t with
                          | `F (`FPred ("_EQ", _)) -> i + 1
                          | _ -> i
                          end in *)
                        fsub, esub @ [i]
                    end in
                  aux fsub esub subt sub
                with InvalidSubFormPath s | InvalidSubExprPath s ->
                  None in
          let open Monads.Option in
          let t = term_of_ipath goal { p with sub = [] } in
          let* fsub, esub = aux [] [] t p.sub in
          Some (boollist_of_intlist fsub, esub) in
        
        let rewrite_data =
          begin match get_eq src, get_term dst with
          | Some (hsub, side), Some (fsub, esub) ->
              Some (false, hsub, side, fsub, esub)
          | _ ->
              begin match get_eq dst, get_term src with
              | Some (hsub, side), Some (fsub, esub) -> Some (true, hsub, side, fsub, esub)
              | _ -> None
              end
          end in

        let ts = sorts sign in
        
        begin match (src, src.ctxt.kind), (dst, dst.ctxt.kind) with

        (* Forward DnD *)
        | (src, `Hyp), (dst, `Hyp) ->
            let t, i =
              let lp = src.sub in
              let rp = dst.sub in
              let lf = (Utils.get_hyp goal src.ctxt.handle).h_form in
              let rf = (Utils.get_hyp goal dst.ctxt.handle).h_form in
              itrace ts sign goal.g_env `Forw lp rp lf rf itr in
            
            begin match rewrite_data with
            (* Rewrite *)
            | Some (eqside, hsub, side, fsub, esub) ->
                let eq_hyp, dst_hyp = if eqside then dst, src else src, dst in
                let fl = Trm.bool_of_bool eqside in
                let h1 =
                  let id = Names.Id.of_string eq_hyp.ctxt.handle in
                  EConstr.mkVar id in
                let id2 = Names.Id.of_string dst_hyp.ctxt.handle in
                let h2 = EConstr.mkVar id2 in
                let h3 =
                  let id = Goal.fresh_name ~basename:(Names.Id.to_string id2) coq_goal () in
                  EConstr.mkVar id in

                let t = Trm.boollist (t @ [side]) in
                
                let hp1 = Trm.boollist hsub in
                let hp2 = Trm.boollist fsub in
                let hp2' = Trm.natlist esub in

                let log t = Log.econstr (Goal.env coq_goal) (Goal.sigma coq_goal) t; Log.str "" in
                if log_dnd_trace then begin
                  log h1;
                  log h2;
                  log h3;
                  log hp1;
                  log hp2;
                  log hp2';
                  log t;
                  log i;
                end;

                let forw = kname "rew_dnd_hyp" in
                calltac forw [ts; fl; h1; h2; h3; hp1; hp2; hp2'; t; i]
            (* Non-rewrite *)
            | None ->
                let h1 =
                  let id = Names.Id.of_string src.ctxt.handle in
                  EConstr.mkVar id in
                let id2 = Names.Id.of_string dst.ctxt.handle in
                let h2 = EConstr.mkVar id2 in
                let h3 =
                  let id = Goal.fresh_name ~basename:(Names.Id.to_string id2) coq_goal () in
                  EConstr.mkVar id in

                let t = Trm.boollist t in

                let hp1 = bool_path src.sub in
                let hp2 = bool_path dst.sub in
                
                let log t = Log.econstr (Goal.env coq_goal) (Goal.sigma coq_goal) t; Log.str "" in
                if log_dnd_trace then begin
                  log h1;
                  log h2;
                  log h3;
                  log hp1;
                  log hp2;
                  log t;
                  log i;
                end;

                let forw = kname "forward" in
                calltac forw [ts; h1; h2; h3; hp1; hp2; t; i]
            end

        (* Backward DnD *)
        | (hyp, `Hyp), (concl, `Concl)
        | (concl, `Concl), (hyp, `Hyp) ->
            let h =
              let id = Names.Id.of_string hyp.ctxt.handle in
              EConstr.mkVar id in
            
            let t, i =
              let lp = hyp.sub in
              let rp = concl.sub in
              let lf = (Utils.get_hyp goal hyp.ctxt.handle).h_form in
              let rf = goal.g_concl in
              itrace ts sign goal.g_env `Back lp rp lf rf itr in
            
            begin match rewrite_data with
            | Some (_, hsub, side, fsub, esub) ->
                let t = Trm.boollist (t @ [side]) in
                
                let hp = Trm.boollist hsub in
                let gp = Trm.boollist fsub in
                let gp' = Trm.natlist esub in

                let log t = Log.econstr (Goal.env coq_goal) (Goal.sigma coq_goal) t; Log.str "" in
                if log_dnd_trace then begin
                  log h;
                  log hp;
                  log gp';
                  log gp;
                  log t;
                  log i;
                end;

                let back = kname "rew_dnd" in
                calltac back [ts; h; hp; gp'; gp; t; i]
            | None ->
                let t = Trm.boollist t in

                let hp = bool_path hyp.sub in
                let gp = bool_path concl.sub in
                
                let log t = Log.econstr (Goal.env coq_goal) (Goal.sigma coq_goal) t; Log.str "" in
                if log_dnd_trace then begin
                  log h;
                  log hp;
                  log gp;
                  log t;
                  log i;
                end;

                let back = kname "back" in
                calltac back [ts; h; hp; gp; t; i]
            end

        | _ -> raise UnexpectedDnD
        end

    | `AInstantiate (wit, tgt) ->
        let l = bool_path (tgt.sub @ [0]) in
        let s = infer_sort goal.g_env wit |> sort_index sign |> Trm.nat_of_int in
        let o = expr sign [] wit in
        let ts = sorts sign in

        let tac, args =
          begin match tgt.ctxt.kind with
          (* Forward instantiate *)
          | `Hyp ->
            let id = Names.Id.of_string tgt.ctxt.handle in
            let h = EConstr.mkVar id in
            let id' = Goal.fresh_name ~basename:(Names.Id.to_string id) coq_goal () in
            let h' = EConstr.mkVar id' in
            kname "inst_hyp", [ts; l; h; h'; s; o]
          (* Backward instantiate *)
          | `Concl ->
              kname "inst_goal", [ts; l; s; o]
          | _ ->
              raise (InvalidPath tgt)
          end in

        calltac tac args

    | `ADuplicate uid ->
        let id = Names.Id.of_string uid in
        let name =
          let name = Goal.fresh_name ~basename:(Names.Id.to_string id) coq_goal () in
          Names.Name.mk_name name in
        let prf = EConstr.mkVar id in

        Tactics.pose_proof name prf

    | `ASimpl tgt | `ARed tgt | `AIndt tgt ->
        let tac_name =
          begin match a with
          | `ASimpl _ -> "simpl_path"
          | `ARed _ -> "unfold_path"
          | `AIndt _ -> "myinduction"
          | _ -> assert false
          end in

        let tac_name, args =
          begin match tgt.ctxt.kind with
          | `Hyp ->
              (* let p = tgt.sub |> fix_sub_eq (`F hyp.h_form) |> Trm.natlist in *)
              let p = tgt.sub |> Trm.natlist in
              let id = Names.Id.of_string tgt.ctxt.handle in
              let h = EConstr.mkVar id in
              tac_name ^ "_hyp", [h; p]
          | `Concl ->
              (* let p = tgt.sub |> fix_sub_eq (`F goal.g_concl) |> Trm.natlist in *)
              let p = tgt.sub |> Trm.natlist in
              tac_name, [p]
          | _ ->
              raise (InvalidPath tgt)
          end in 

        calltac (kname tac_name) args
        
    | _ ->
        raise (UnsupportedAction a)
end
