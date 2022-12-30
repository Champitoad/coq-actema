open Proofview
open CoqUtils
open Utils
open Extlib

module UidMap = Map.Make(Uid)

type hidmap = Names.Id.t UidMap.t

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
  module SortSymbol = BiMap(Symbol)(String)
  module SymbolMap = Map.Make(Symbol)

  type symbols =
    { s_sorts : SortSymbol.t; s_funcs : SortSymbol.t; s_preds : SortSymbol.t }
  
  type typing =
    { t_funcs : Fo_t.sig_ NameMap.t; t_preds : Fo_t.arity NameMap.t }
  
  type t =
    { symbols : symbols; typing : typing; defaults : EConstr.t SymbolMap.t }
end

let peano : FOSign.t =
  let open FOSign in
  let open Trm in
  let nat : Fo_t.type_ = `TVar ("nat", 0) in
  let symbols =
    let open SortSymbol in
    let s_sorts = empty |>
      add (Ind nat_name) "nat" in
    let s_funcs = empty |>
      add (Ctr zero_name) "Z" |>
      add (Ctr succ_name) "S" |> fun m ->
      List.fold_left (fun m name -> add (Cst name) "add" m) m Trm.add_names |> fun m ->
      List.fold_left (fun m name -> add (Cst name) "mult" m) m Trm.mul_names in
    let s_preds = empty in
    { s_sorts; s_funcs; s_preds } in
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
(** Exporting Coq goals to Actema *)

module Export = struct
  let fosign (sign : EConstr.t) : FOSign.t =
    failwith "TODO"

  let dummy_expr : Logic_t.expr =
    `EFun ("dummy", [])

  let dummy_form : Logic_t.form =
    `FPred ("dummy", [])

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
    { env : Environ.env; evd : Evd.evar_map; sign : FOSign.t }
  
  type destarg = destenv * EConstr.types

  type sdest = destarg -> symbol

  let trydest f g =
    fun x -> try f x with Constr.DestKO -> g x

  let ( >>? ) = trydest

  let dest_sconst : sdest = fun ({ evd; _ }, t) ->
    Cst (EConstr.destConst evd t |> fst)

  let dest_sconstruct : sdest = fun ({ env; evd; _ }, t) ->
    Ctr (EConstr.destConstruct evd t |> fst)
  
  let dest_sind : sdest = fun ({ evd; _ }, t) ->
    Ind (EConstr.destInd evd t |> fst)
  
  let dest_svar : sdest = fun ({ evd; _ }, t) ->
    Var (EConstr.destVar evd t)

  let dest_symbol : sdest =
    dest_sconst >>?
    dest_sconstruct >>?
    dest_sind >>?
    dest_svar

  let find_sort ({ sign; _ }, _ as d : destarg) : string =
    try
      FOSign.SortSymbol.find (dest_symbol d) sign.symbols.s_sorts
    with Not_found ->
      raise Constr.DestKO

  let find_func ({ sign; _ }, _ as d : destarg) : Fo_t.name * Fo_t.sig_ =
    try
      let name = FOSign.SortSymbol.find (dest_symbol d) sign.symbols.s_funcs in
      let sig_ = NameMap.find name sign.typing.t_funcs in
      name, sig_
    with Not_found ->
      raise Constr.DestKO

  let find_pred ({ sign; _ }, _ as d : destarg) : Fo_t.name * Fo_t.arity =
    try
      let name = FOSign.SortSymbol.find (dest_symbol d) sign.symbols.s_preds in
      let arity = NameMap.find name sign.typing.t_preds in
      name, arity
    with Not_found ->
      raise Constr.DestKO

  let dest_functy ({ evd; _ } as e, t : destarg) : Fo_t.sig_ =
    let rec aux arity t =
      if EConstr.isProd evd t then
        let _, t1, t2 = EConstr.destProd evd t in
        aux (`TVar (find_sort (e, t1), 0) :: arity) t2
      else
        arity, `TVar (find_sort (e, t), 0) in
    aux [] t

  let dest_predty ({ evd; _ } as e, t : destarg) : Fo_t.arity =
    let rec aux arity t =
      if EConstr.isProd evd t then
        let _, t1, t2 = EConstr.destProd evd t in
        aux (`TVar (find_sort (e, t1), 0) :: arity) t2
      else
        if t |> EConstr.to_constr evd |> Constr.destSort |> Sorts.is_prop then
          arity
        else
          raise Constr.DestKO in
    aux [] t
  
  
  type edest = destarg -> Logic_t.expr

  let rec dest_econst : edest = fun (e, t) ->
    match find_func (e, t) with
    | name, ([], _) ->
        `EFun (name, [])
    | _ -> raise Constr.DestKO
  
  and dest_evar : edest = fun ({ env; evd; _ }, t) ->
    let id = EConstr.destVar evd t |> Names.Id.to_string in
    `EVar (id, 0)

  and dest_erel : edest = fun ({ env; evd; _ }, t) ->
    let n = EConstr.destRel evd t in
    let name =
      EConstr.lookup_rel n env |>
      EConstr.to_rel_decl evd |>
      Context.Rel.Declaration.get_name in
    match name with
    | Name id -> `EVar (Names.Id.to_string id, 0)
    | _ -> raise Constr.DestKO

  and dest_eapp : edest = fun ({ evd; _ } as e, t) ->
    let head, args = EConstr.destApp evd t in
    match find_func (e, head) with
    | name, _ ->
        let targs = Array.map (fun u -> dest_expr (e, u)) args in
        `EFun (name, Array.to_list targs)

  and dest_expr : edest = fun et ->
    begin
      dest_econst >>?
      dest_evar >>?
      dest_erel >>?
      dest_eapp >>?
      fun _ -> dummy_expr
    end et


  type fdest = destarg -> Logic_t.form

  let rec dest_pconst : fdest = fun ({ env; evd; _ } as e, t) ->
    if not (is_prop env evd t) then raise Constr.DestKO;
    let name, _ = find_pred (e, t) in
    `FPred (name, [])

  and dest_pvar : fdest = fun ({ env; evd; _ }, t) ->
    if not (is_prop env evd t) then raise Constr.DestKO;
    let name = EConstr.destVar evd t |> Names.Id.to_string in
    `FPred (name, [])

  and dest_papp : fdest = fun ({ env; evd; _ } as e, t) ->
    if not (is_prop env evd t) then raise Constr.DestKO;
    let head, args = EConstr.destApp evd t in
    match find_pred (e, head) with
    | name, _ ->
        let targs = Array.map (fun u -> dest_expr (e, u)) args in
        `FPred (name, Array.to_list targs)

  and dest_eq : fdest = fun ({ env; evd; _ } as e, t) ->
    let head, args = EConstr.destApp evd t in
    let (mind, i), _ = EConstr.destInd evd head in
    let head_is_eq =
      Names.(KerName.equal (MutInd.canonical mind) (Trm.Logic.kname "eq")) && i = 0 in
    match head_is_eq, args with
    | true, [| _; t1; t2 |] ->
        let e1 = dest_expr (e, t1) in
        let e2 = dest_expr (e, t2) in
        `FPred ("_EQ", [e1; e2])
    | _ ->
        raise Constr.DestKO

  and dest_true : fdest = fun ({ env; evd; _ }, t) ->
    match name_of_inductive env evd t with
    | "True" ->
        `FTrue
    | name ->
        raise Constr.DestKO

  and dest_false : fdest = fun ({ env; evd; _ }, t) ->
    match name_of_inductive env evd t with
    | "False" ->
        `FFalse
    | name ->
        raise Constr.DestKO

  and dest_imp : fdest = fun ({ env; evd; _ } as e, t) ->
    let x, t1, t2 = EConstr.destProd evd t in
    if not (is_imp (env, evd) x t1 t2) then raise Constr.DestKO;
    let env =
      (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (x, t1)) env) in
    `FConn (`Imp, [dest_form (e, t1); dest_form ({ e with env }, t2)])

  and dest_and : fdest = fun ({ env; evd; _ } as e, t) ->
    let f, args  = EConstr.destApp evd t in
    match name_of_inductive env evd f, Array.to_list args with
    | "and", [t1; t2] ->
        `FConn (`And, [dest_form (e, t1); dest_form (e, t2)])
    | name, _ ->
        raise Constr.DestKO

  and dest_or : fdest = fun ({ env; evd; _ } as e, t) ->
    let f, args  = EConstr.destApp evd t in
    match name_of_inductive env evd f, Array.to_list args with
    | "or", [t1; t2] ->
        `FConn (`Or, [dest_form (e, t1); dest_form (e, t2)])
    | name, _ ->
        raise Constr.DestKO

  and dest_iff : fdest = fun ({ evd; _ } as e, t) ->
    let f, args  = EConstr.destApp evd t in
    match name_of_const evd f, Array.to_list args with
    | "iff", [t1; t2] ->
        `FConn (`Equiv, [dest_form (e, t1); dest_form (e, t2)])
    | name, _ ->
        raise Constr.DestKO

  and dest_not : fdest = fun ({ evd; _ } as e, t) ->
    let f, args  = EConstr.destApp evd t in
    match name_of_const evd f, Array.to_list args with
    | "not", [t1] ->
        `FConn (`Not, [dest_form (e, t1)])
    | name, _ ->
        raise Constr.DestKO
  
  and dest_forall : fdest = fun ({ env; evd; _ } as e, t) ->
    let x, t1, t2 = EConstr.destProd evd t in
    let sort = find_sort (e, t1) in
    match Context.binder_name x with
    | Name id ->
        let name = Names.Id.to_string id in 
        let ty = `TVar (sort, 0) in
        let env =
          (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (x, t1)) env) in
        let body = dest_form ({ e with env }, t2) in
        `FBind (`Forall, name, ty, body)
    | _ -> raise Constr.DestKO
  
  and dest_exists : fdest = fun ({ env; evd; _ } as e, t) ->
    let head, args = EConstr.destApp evd t in
    let (mind, i), _ = EConstr.destInd evd head in
    let head_is_ex =
      Names.(KerName.equal (MutInd.canonical mind) (Trm.Logic.kname "ex")) && i = 0 in
    match head_is_ex, args with
    | true, [| _; t2 |] ->
        let x, t1, t2 = EConstr.destLambda evd t2 in
        let sort = find_sort (e, t1) in
        begin match Context.binder_name x with
        | Name id ->
            let name = Names.Id.to_string id in
            let ty = `TVar (sort, 0) in
            let env =
              (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (x, t1)) env) in
            let body = dest_form ({ e with env }, t2) in
            `FBind (`Exist, name, ty, body)
        | _ -> raise Constr.DestKO
        end
    | _ -> raise Constr.DestKO
  
  and dest_form : fdest = fun et ->
    begin
      dest_eq >>?
      dest_true >>?
      dest_false >>?
      dest_pconst >>?
      dest_pvar >>?
      dest_papp >>?
      dest_imp >>?
      dest_and >>?
      dest_or >>?
      dest_iff >>?
      dest_not >>?
      dest_forall >>?
      dest_exists >>?
      fun _ -> dummy_form
    end et


  type varenv = Logic_t.bvar list NameMap.t
  type varsign = varenv * FOSign.t

  let shortname (fullname : string) : string =
    fullname |> String.split_on_char '.' |> List.rev |> List.hd

  let env_of_varsign ((venv, sign) : varsign) : Logic_t.env =
    let open FOSign in

    let env_sort =
      SortSymbol.values sign.symbols.s_sorts in
    let env_sort_name =
      List.(combine env_sort (map shortname env_sort)) in

    let func_names = SortSymbol.values sign.symbols.s_funcs in
    let env_fun =
      ("dummy", ([], `TVar ("unit", 0))) ::
      List.map (fun f -> f, NameMap.find f sign.typing.t_funcs) func_names in
    let env_fun_name =
      List.(combine func_names (map shortname func_names)) in

    let pred_names = SortSymbol.values sign.symbols.s_preds in
    let env_prp =
      ("dummy", []) ::
      List.map (fun p -> p, NameMap.find p sign.typing.t_preds) pred_names in
    let env_prp_name =
      List.(combine pred_names (map shortname pred_names)) in

    let env_var = NameMap.bindings venv in

    let env_handles = [] in

    { env_sort; env_sort_name; env_fun; env_fun_name; env_prp; env_prp_name;
      env_var; env_handles }
  
  let env ({ env = coq_env; evd; sign } as e : destenv) : Fo_t.env * FOSign.t = 
    let open FOSign in

    let add_sort name sy ty (env, sign) =
      let sort = ty |> EConstr.destSort evd |> EConstr.ESorts.kind evd in
      if sort <> Sorts.set && sort <> Sorts.type1 then
        raise Constr.DestKO;
      let s_sorts = SortSymbol.add sy name sign.symbols.s_sorts in
      let symbols = { sign.symbols with s_sorts } in
      env, { sign with symbols } in
    
    let add_default t ty (env, sign) =
      let sort_sy = dest_symbol ({ env = coq_env; evd; sign }, ty) in
      if not (SortSymbol.mem sort_sy sign.symbols.s_sorts)
           || SymbolMap.mem sort_sy sign.defaults then
        raise Constr.DestKO;
      (env, { sign with defaults = SymbolMap.add sort_sy t sign.defaults }) in
    
    let add_func name sy ty (env, sign) =
      let e = { e with sign } in
      let sig_ = dest_functy (e, ty) in
      let s_funcs = SortSymbol.add sy name sign.symbols.s_funcs in
      let t_funcs = NameMap.add name sig_ sign.typing.t_funcs in
      let symbols = { sign.symbols with s_funcs } in
      let typing = { sign.typing with t_funcs } in
      env, { sign with symbols; typing } in

    let add_strict_func name sy ty (env, sign) =
      let e = { e with sign } in
      let sig_ = dest_functy (e, ty) in
      if List.length (fst sig_) = 0 then raise Constr.DestKO;
      let s_funcs = SortSymbol.add sy name sign.symbols.s_funcs in
      let t_funcs = NameMap.add name sig_ sign.typing.t_funcs in
      let symbols = { sign.symbols with s_funcs } in
      let typing = { sign.typing with t_funcs } in
      env, { sign with symbols; typing } in

    let add_pred name sy ty (env, sign) =
      let e = { e with sign } in
      let arity = dest_predty (e, ty) in
      let s_preds = SortSymbol.add sy name sign.symbols.s_preds in
      let t_preds = NameMap.add name arity sign.typing.t_preds in
      let symbols = { sign.symbols with s_preds } in
      let typing = { sign.typing with t_preds } in
      env, { sign with symbols; typing } in

    let add_var name ty value (env, sign) =
      let e = { e with sign } in
      let sort = find_sort (e, ty) in
      let destenv = { env = coq_env; evd; sign } in
      let body = Option.map (fun v -> dest_expr (destenv, EConstr.of_constr v)) value in
      NameMap.add name [`TVar (sort, 0), body] env, sign in

    (* Add sorts defined as inductive types *)
    let venv, sign = Environ.fold_inductives begin fun mi bodies vsign ->
        let _, vsign = Array.fold_left begin fun (i, vsign) body ->
            let id = mi, i in
            let modpath = Names.(Ind.modpath id |> ModPath.to_string) in
            let name =
              let name = Names.Id.to_string body.Declarations.mind_typename in
              Printf.sprintf "%s.%s" modpath name in
            let ty =
              match body.Declarations.mind_arity with
              | RegularArity ar -> EConstr.of_constr ar.mind_user_arity
              | TemplateArity ar -> EConstr.mkType ar.template_level in
            i+1, vsign |> begin
              add_sort name (Ind id) ty >>?
              identity
            end
          end (0, vsign) bodies.mind_packets in
        vsign
      end coq_env (NameMap.empty, sign) in
    
    (* Add sorts, default elements, functions and predicates defined as global
       constants *)
    let venv, sign = Environ.fold_constants begin fun c _ vsign ->
        let t = EConstr.mkConst c in
        (* let name = name_of_const evd t in *)
        let name = c |> Names.Constant.to_string in
        let ty =
          Environ.constant_type_in coq_env (Univ.in_punivs c) |>
          EConstr.of_constr in
        vsign |> begin
          add_sort name (Cst c) ty >>?
          add_default t ty >>?
          add_func name (Cst c) ty >>?
          add_pred name (Cst c) ty >>?
          identity
        end
      end coq_env (venv, sign) in

    (* Add sorts, default elements, functions, predicates and variables defined
       as local variables *)
    let venv, sign = Environ.fold_named_context begin fun _ decl vsign ->
        let id = Context.Named.Declaration.get_id decl in
        let name = id |> Names.Id.to_string in
        let ty = decl |> Context.Named.Declaration.get_type |> EConstr.of_constr in
        let value = Context.Named.Declaration.get_value decl in
        vsign |> begin
          add_sort name (Var id) ty >>?
          add_default (EConstr.mkVar id) ty >>?
          add_strict_func name (Var id) ty >>?
          add_pred name (Var id) ty >>?
          add_var name ty value >>?
          identity
        end
      end coq_env ~init:(venv, sign) in

    env_of_varsign (venv, sign), sign

  let hyps ({ env = coq_env; evd; _} as destenv : destenv) : Logic_t.hyp list * hidmap =
    let fresh = Uid.fresh () in
    Environ.fold_named_context begin fun _ decl (hyps, hm) ->
      let name = Context.Named.Declaration.get_id decl in
      let ty = decl |> Context.Named.Declaration.get_type |> EConstr.of_constr in
      if is_prop coq_env evd ty then
        let h_id = fresh () in
        let h_form = dest_form (destenv, ty) in
        let hyp = Logic_t.{ h_id; h_form } in
        (hyp :: hyps, UidMap.add h_id name hm)
      else
        (hyps, hm)
    end coq_env ~init:([], UidMap.empty)

  let goal (sign : FOSign.t) (goal : Goal.t) : FOSign.t * Logic_t.goal * hidmap =
    let coq_env = Goal.env goal in
    let evd = Goal.sigma goal in
    let concl = Goal.concl goal in
    
    let destenv = { env = coq_env; evd; sign } in

    let g_env, sign =
      env destenv in
    (* Second pass to get all constants with previously unknown sorts *)
    let g_env, sign =
      env { destenv with sign } in
    
    let (g_hyps, hm) =
      hyps { destenv with sign } in

    let g_concl : Logic_t.form =
      dest_form ({ destenv with sign }, concl) in
    
    sign, Logic_t.{ g_env; g_hyps; g_concl }, hm
end

(* -------------------------------------------------------------------- *)
(** Importing Actema actions as Coq tactics *)

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
      List.map (fun sy -> FOSign.SortSymbol.find sy sign.symbols.s_sorts) in
    List.nth_index 0 s sorts
  
  let infer_sort (env : Logic_t.env) (e : Logic_t.expr) : string =
    match einfer env e with
    | `TVar (name, _) -> name
    | _ -> failwith "Non-atomic sort type"
    
  let nth_sort (sign : FOSign.t) (n : int) : EConstr.t =
    let sorts = sign.symbols.s_sorts |> FOSign.SortSymbol.keys in
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
    | `TVar (x, _) ->
        symbol (FOSign.SortSymbol.dnif x sign.symbols.s_sorts)
    | `TUnit ->
        Trm.unit
    | _ ->
        failwith "Unsupported type"
  
  let rec expr (sign : FOSign.t) (lenv : Logic_t.lenv)
      (e : Fo_t.expr) : EConstr.t =
    match e with
    | `EVar (x, i) ->
        if LEnv.exists lenv (x, i) then begin
          let index : int =
            List.(lenv |> split |> fst |> nth_index i x) in
          EConstr.mkRel (index + 1)
        end else
          Trm.var x
    | `EFun (f, args) ->
        let head = symbol (FOSign.SortSymbol.dnif f sign.symbols.s_funcs) in
        let args = List.map (expr sign lenv) args in
        EConstr.mkApp (head, Array.of_list args)

  let rec expr_itrace (sign : FOSign.t)
      (env : Logic_t.env) (lenv : Logic_t.lenv) (side : int)
      (e : Fo_t.expr) : EConstr.t =
    match e with
    | `EVar (x, i) ->
        if LEnv.exists lenv (x, i) then begin
          let s = sort_index sign (infer_sort (Utils.Vars.push_lenv env lenv) e) in
          let index : int =
            List.(lenv |> split |> fst |> nth_index i x) in
          let env_index = if side = 0 then 2 else 1 in
          EConstr.(mkApp (mkRel env_index, Trm.[| nat_of_int s; nat_of_int index |]))
        end else
          Trm.var x
    | `EFun (f, args) ->
        let head = symbol (FOSign.SortSymbol.dnif f sign.symbols.s_funcs) in
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
        let head = symbol (FOSign.SortSymbol.dnif p sign.symbols.s_preds) in
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

  let action (sign : FOSign.t) (hm : hidmap) (goal : Logic_t.goal) (coq_goal : Goal.t)
             (a : Logic_t.action) : unit tactic =
    let open Proofview.Monad in
    match a with
    | `AId ->
        Tacticals.tclIDTAC
    | `AExact id ->
        let name = UidMap.find id hm in
        Tactics.exact_check (EConstr.mkVar name)
    | `ADef (x, _, e) ->
        let id = Names.Id.of_string x in
        let name = Names.Name.Name id in
        let body = expr sign [] e in
        Tactics.pose_tac name body
    | `ACut (f, _) ->
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
                  Tactics.left Tactypes.NoBindings >>= fun _ -> aux zero (n-1)
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
        let id = UidMap.find uid hm in
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
              Some (hsub, side, fsub, esub)
          | _ ->
              begin match get_eq dst, get_term src with
              | Some (hsub, side), Some (fsub, esub) -> Some (hsub, side, fsub, esub)
              | _ -> None
              end
          end in

        let ts = sorts sign in
        
        begin match (src, src.ctxt.kind), (dst, dst.ctxt.kind) with

        (* Forward DnD *)
        | (hyp1, `Hyp), (hyp2, `Hyp) ->
            let h1 =
              let id = UidMap.find hyp1.ctxt.handle hm in
              EConstr.mkVar id in
            let id2 = UidMap.find hyp2.ctxt.handle hm in
            let h2 = EConstr.mkVar id2 in
            let h3 =
              let id = Goal.fresh_name ~basename:(Names.Id.to_string id2) coq_goal () in
              EConstr.mkVar id in

            let t, i =
              let lp = hyp1.sub in
              let rp = hyp2.sub in
              let lf = (Utils.get_hyp goal hyp1.ctxt.handle).h_form in
              let rf = (Utils.get_hyp goal hyp2.ctxt.handle).h_form in
              itrace ts sign goal.g_env `Forw lp rp lf rf itr in
            
            begin match rewrite_data with
            | Some (hsub, side, fsub, esub) ->
                let t = Trm.boollist (t @ [not side]) in
                
                let hp1 = Trm.boollist hsub in
                let hp2 = Trm.boollist fsub in
                let hp2' = Trm.natlist esub in

                let log_trace () =
                  let log t = Log.econstr (Goal.env coq_goal) (Goal.sigma coq_goal) t; Log.str "" in
                  log h1;
                  log h2;
                  log h3;
                  log hp1;
                  log hp2;
                  log hp2';
                  log t;
                  log i in
                log_trace ();

                let forw = kname "rew_dnd_hyp" in
                calltac forw [ts; h1; h2; h3; hp1; hp2; hp2'; t; i]
            | None ->
                let t = Trm.boollist t in

                let hp1 = bool_path hyp1.sub in
                let hp2 = bool_path hyp2.sub in
                
                let log_trace () =
                  let log t = Log.econstr (Goal.env coq_goal) (Goal.sigma coq_goal) t; Log.str "" in
                  log h1;
                  log h2;
                  log h3;
                  log hp1;
                  log hp2;
                  log t;
                  log i in
                log_trace ();

                let forw = kname "forward" in
                calltac forw [ts; h1; h2; h3; hp1; hp2; t; i]
            end

        (* Backward DnD *)
        | (hyp, `Hyp), (concl, `Concl)
        | (concl, `Concl), (hyp, `Hyp) ->
            let h =
              let id = UidMap.find hyp.ctxt.handle hm in
              EConstr.mkVar id in
            
            let t, i =
              let lp = hyp.sub in
              let rp = concl.sub in
              let lf = (Utils.get_hyp goal hyp.ctxt.handle).h_form in
              let rf = goal.g_concl in
              itrace ts sign goal.g_env `Back lp rp lf rf itr in
            
            begin match rewrite_data with
            | Some (hsub, side, fsub, esub) ->
                let t = Trm.boollist (t @ [side]) in
                
                let hp = Trm.boollist hsub in
                let gp = Trm.boollist fsub in
                let gp' = Trm.natlist esub in

                let log_trace () =
                  let log t = Log.econstr (Goal.env coq_goal) (Goal.sigma coq_goal) t; Log.str "" in
                  log h;
                  log hp;
                  log gp';
                  log gp;
                  log t;
                  log i; in
                log_trace ();

                let back = kname "rew_dnd" in
                calltac back [ts; h; hp; gp'; gp; t; i]
            | None ->
                let t = Trm.boollist t in

                let hp = bool_path hyp.sub in
                let gp = bool_path concl.sub in
                
                let log_trace () =
                  let log t = Log.econstr (Goal.env coq_goal) (Goal.sigma coq_goal) t; Log.str "" in
                  log h;
                  log hp;
                  log gp;
                  log t;
                  log i; in
                log_trace ();

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
            let id = UidMap.find tgt.ctxt.handle hm in
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
        let id = UidMap.find uid hm in
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
              let hyp = Utils.get_hyp goal tgt.ctxt.handle in
              (* let p = tgt.sub |> fix_sub_eq (`F hyp.h_form) |> Trm.natlist in *)
              let p = tgt.sub |> Trm.natlist in
              let id = UidMap.find tgt.ctxt.handle hm in
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

  (* let rec proof (sign : FOSign.t) (hm : hidmap) (t : Logic_t.proof) : unit tactic =
    let open Proofview.Monad in
    match t with
    | `PNode (a, goal, ipat, subs) ->
        Goal.enter begin fun coq_goal ->
          action sign hm goal coq_goal ipat a >>= fun hm ->
          if subs = [] then 
            Tacticals.tclIDTAC
          else
            let subs_tacs = Stdlib.List.map (proof sign hm) subs in
            Proofview.tclDISPATCH subs_tacs
        end *)
end
