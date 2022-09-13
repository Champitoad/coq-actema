open Proofview
open CoqUtils

module Uid : sig
  include Map.OrderedType

  val fresh : unit -> unit -> t
end with type t = Logic_t.uid = struct
  type t = Logic_t.uid
  
  let compare = Int.compare

  let fresh () : unit -> t =
    let count = ref (-1) in
    fun () -> incr count; !count
end

module UidMap = Map.Make(Uid)

type hidmap = Names.Id.t UidMap.t

module KNameMap = Map.Make(Names.KerName)

type cstmap = (Fo_t.name * Fo_t.sig_) KNameMap.t
type pstmap = (Fo_t.name * Fo_t.arity) KNameMap.t

type fosign =
  { sorts : string KNameMap.t; funcs : cstmap; preds : pstmap }

module type FOSign = sig
  val sign : fosign
end

module Peano : FOSign = struct
  let nat : Fo_t.type_ = `TVar ("nat", 0)
  let sign : fosign =
    let open KNameMap in
    let sorts =
      empty |>
      add Trm.nat_kname "nat" in
    let funcs =
      empty |>
      add Trm.zero_kname ("Z", ([], nat)) |>
      add Trm.succ_kname ("S", ([nat], nat)) |>
      add Trm.add_kname ("add", ([nat; nat], nat)) |>
      add Trm.mul_kname ("mult", ([nat; nat], nat)) in
    let preds =
      empty in
    { sorts; funcs; preds }
end

(* -------------------------------------------------------------------- *)
(** Exporting Coq goals to Actema *)

module Export (S : FOSign) = struct
  let fosign (sign : EConstr.t) : fosign =
    failwith "TODO"

  let name_of_const evd t =
    EConstr.destConst evd t |> fst |>
    Names.Constant.repr2 |> snd |> Names.Label.to_string

  let name_of_construct evd t =
    let name, _ = EConstr.destConstruct evd t in
    name |> Names.Construct.modpath |> Names.ModPath.to_string

  let name_of_inductive env evd t =
    let name, _ = EConstr.destInd evd t in
    Printer.pr_inductive env name |> Pp.string_of_ppcmds

  let dummy_expr : Logic_t.expr =
    `EFun ("dummy", [])

  let dummy_form : Logic_t.form =
    `FPred ("dummy", [])

  type edest = ((Environ.env * Evd.evar_map) * EConstr.types) -> Logic_t.expr
  type fdest = ((Environ.env * Evd.evar_map) * EConstr.types) -> Logic_t.form

  let comp_edest (d1 : edest) (d2 : edest) : edest = fun et ->
    try d1 et with Constr.DestKO -> d2 et
  let comp_fdest (d1 : fdest) (d2 : fdest) : fdest = fun et ->
    try d1 et with Constr.DestKO -> d2 et

  let ( >>!! ) = comp_edest
  let ( >>! ) = comp_fdest

  let is_prop env evd term =
    let sort = Retyping.get_sort_of env evd term in
    Sorts.is_prop sort

  let is_imp (env, evd) x t1 t2 : bool = 
    is_prop env evd t1
    && is_prop
        (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (x, t1)) env)
        evd t2
    && (x.Context.binder_name = Names.Anonymous || EConstr.Vars.noccurn evd 1 t2)

  let get_func (env, evd) t : Fo_t.name * Fo_t.sig_ =
    let kname =
      try
        EConstr.destConst evd t |> fst |> Names.Constant.canonical
      with Constr.DestKO ->
        EConstr.destConstruct evd t |> fst |> construct_kname env in
    try
      KNameMap.find kname S.sign.funcs
    with Not_found ->
      raise Constr.DestKO
    
  let rec dest_econst : edest = fun ((env, evd), t) ->
    match get_func (env, evd) t with
    | name, ([], _) ->
        `EFun (name, [])
    | _ -> raise Constr.DestKO

  and dest_eapp : edest = fun ((env, evd), t) ->
    let head, args = EConstr.destApp evd t in
    match get_func (env, evd) head with
    | name, _ ->
        let targs = Array.map (fun u -> dest_expr ((env, evd), u)) args in
        `EFun (name, Array.to_list targs)

  and dest_pvar : fdest = fun ((env, evd), t) ->
    if not (is_prop env evd t) then raise Constr.DestKO;
    let name = EConstr.destVar evd t |> Names.Id.to_string in
    `FPred (name, [])

  and dest_pconst : fdest = fun ((env, evd), t) ->
    if not (is_prop env evd t) then raise Constr.DestKO;
    let name = name_of_const evd t in
    `FPred (name, [])

  and dest_eq : fdest = fun ((env, evd), t) ->
    if not (is_prop env evd t) then raise Constr.DestKO;
    let head, args = EConstr.destApp evd t in
    let (mind, i), _ = EConstr.destInd evd head in
    let head_is_eq =
      Names.(KerName.equal (MutInd.canonical mind) Trm.eq_kname) && i = 0 in
    match head_is_eq, args with
    | true, [| _; t1; t2 |] ->
        let e1 = dest_expr ((env, evd), t1) in
        let e2 = dest_expr ((env, evd), t2) in
        `FPred ("_EQ", [e1; e2])
    | _ ->
        raise Constr.DestKO

  and dest_true : fdest = fun ((env, evd), t) ->
    match name_of_inductive env evd t with
    | "True" ->
        `FTrue
    | name ->
        raise Constr.DestKO

  and dest_false : fdest = fun ((env, evd), t) ->
    match name_of_inductive env evd t with
    | "False" ->
        `FFalse
    | name ->
        raise Constr.DestKO

  and dest_imp : fdest = fun ((_, evd as e), t) ->
    let x, t1, t2 = EConstr.destProd evd t in
    if not (is_imp e x t1 t2) then raise Constr.DestKO;
    `FConn (`Imp, [dest_form (e, t1); dest_form (e, t2)])

  and dest_and : fdest = fun ((env, evd as e), t) ->
    let f, args  = EConstr.destApp evd t in
    match name_of_inductive env evd f, Array.to_list args with
    | "and", [t1; t2] ->
        `FConn (`And, [dest_form (e, t1); dest_form (e, t2)])
    | name, _ ->
        raise Constr.DestKO

  and dest_or : fdest = fun ((env, evd as e), t) ->
    let f, args  = EConstr.destApp evd t in
    match name_of_inductive env evd f, Array.to_list args with
    | "or", [t1; t2] ->
        `FConn (`Or, [dest_form (e, t1); dest_form (e, t2)])
    | name, _ ->
        raise Constr.DestKO

  and dest_iff : fdest = fun ((env, evd as e), t) ->
    let f, args  = EConstr.destApp evd t in
    match name_of_const evd f, Array.to_list args with
    | "iff", [t1; t2] ->
        `FConn (`Equiv, [dest_form (e, t1); dest_form (e, t2)])
    | name, _ ->
        raise Constr.DestKO

  and dest_not : fdest = fun ((env, evd as e), t) ->
    let f, args  = EConstr.destApp evd t in
    match name_of_const evd f, Array.to_list args with
    | "not", [t1] ->
        `FConn (`Not, [dest_form (e, t1)])
    | name, _ ->
        raise Constr.DestKO

  and dest_expr : edest = fun et ->
    begin
      dest_econst >>!!
      dest_eapp >>!!
      fun _ -> dummy_expr
    end et
  
  and dest_form : fdest = fun et ->
    begin
      dest_eq >>!
      dest_true >>!
      dest_false >>!
      dest_pconst >>!
      dest_pvar >>!
      dest_imp >>!
      dest_and >>!
      dest_or >>!
      dest_iff >>!
      dest_not >>!
      fun _ -> dummy_form
    end et

  let empty_env : Logic_t.env =
    let env_tvar =
      KNameMap.bindings S.sign.sorts |> List.split |> snd |>
      List.map (fun name -> (name, [])) in
    let env_fun =
      ("dummy", ([], `TVar ("unit", 0))) ::
      (KNameMap.bindings S.sign.funcs |> List.split |> snd) in
    let env_prp =
      ("dummy", []) ::
      (KNameMap.bindings S.sign.preds |> List.split |> snd) in
    { env_prp; env_fun; env_var = []; env_tvar; env_handles = [] }

  let env (coq_env : Environ.env) (evd : Evd.evar_map) : Logic_t.env =
    let add_pvar isprop name env =
      let env_prp =
        try
          if isprop () then
            (name, []) :: env.Fo_t.env_prp
          else
            env.Fo_t.env_prp
        with e when CErrors.is_anomaly e ->
            env.Fo_t.env_prp in
      { env with env_prp } in

    let env = empty_env in

    let env = Environ.fold_constants begin fun c _ env ->
        let isprop () = is_prop coq_env evd (EConstr.mkConst c) in
        let name = name_of_const evd (EConstr.mkConst c) in
        add_pvar isprop name env
      end coq_env env in

    let env = Environ.fold_named_context begin fun _ decl env ->
        let name = Context.Named.Declaration.get_id decl |> Names.Id.to_string in
        let ty = decl |> Context.Named.Declaration.get_type |> EConstr.of_constr in
        let isprop () = ty |> EConstr.to_constr evd |> Constr.destSort |> Sorts.is_prop in
        add_pvar isprop name env
      end coq_env ~init:env in

    env

  let hyps (coq_env : Environ.env) (evd : Evd.evar_map) : Logic_t.hyp list * hidmap =
    let fresh = Uid.fresh () in
    Environ.fold_named_context begin fun _ decl (hyps, hm) ->
      let name = Context.Named.Declaration.get_id decl in
      let ty = decl |> Context.Named.Declaration.get_type |> EConstr.of_constr in
      if is_prop coq_env evd ty then
        let h_id = fresh () in
        let h_form = dest_form ((coq_env, evd), ty) in
        let hyp = Logic_t.{ h_id; h_form } in
        (hyp :: hyps, UidMap.add h_id name hm)
      else
        (hyps, hm)
    end coq_env ~init:([], UidMap.empty)

  let goal (goal : Goal.t) : Logic_t.goal * hidmap =
    let coq_env = Goal.env goal in
    let evd = Goal.sigma goal in
    let coq_concl = Goal.concl goal in

    let g_env : Logic_t.env =
      env coq_env evd in

    let (g_hyps, hm) : Logic_t.hyp list * hidmap =
      hyps coq_env evd in

    let g_concl : Logic_t.form =
      dest_form ((coq_env, evd), coq_concl) in
    
    Logic_t.{ g_env; g_hyps; g_concl }, hm
end

(* -------------------------------------------------------------------- *)
(** Importing Actema actions as Coq tactics *)

module Import (S : FOSign) = struct
  let fosign () : EConstr.t =
    failwith "TODO"

  let get_hyps_names (coq_goal : Goal.t) =
    Goal.hyps coq_goal |> Context.Named.to_vars

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

  exception UnsupportedAction of Logic_t.action
  exception UnexpectedIntroPattern of Logic_t.intro_pat
  exception UnexpectedIntroVariant of int
  exception UnexpectedDnD

  let action (hm : hidmap) (goal : Logic_t.goal) (coq_goal : Goal.t)
             (ipat : Logic_t.intro_pat) (a : Logic_t.action) : hidmap tactic =
    let open Proofview.Monad in
    match a with
    | `AId ->
        Tacticals.tclIDTAC >>= fun () ->
        return hm
    | `AExact id ->
        let name = UidMap.find id hm in
        Tactics.exact_check (EConstr.mkVar name) >>= fun _ ->
        return hm
    | `AIntro (iv, wit) ->
        begin match goal.g_concl with
        | `FTrue ->
            Tactics.one_constructor 1 Tactypes.NoBindings >>= fun _ ->
            return hm
        | `FConn (`Imp, _) | `FConn (`Not, _) ->
            (* Generate fresh Coq identifier for intro *)
            let base_name = Names.Id.of_string "H" in
            let hyps_names = get_hyps_names coq_goal in
            let name = Namegen.next_ident_away base_name hyps_names in
            (* Apply intro *)
            let pat = mk_intro_patterns [name] in
            Tactics.intro_patterns false pat >>= fun _ ->
            (* Retrieve associated Actema identifier from intro pattern *)
            let id = match ipat with
                    | [[id]] -> id
                    | _ -> raise (UnexpectedIntroPattern ipat) in
            (* Add it to the hidmap *)
            return (UidMap.add id name hm)
        | `FConn (`And, _) | `FConn (`Equiv, _) ->
            Tactics.split Tactypes.NoBindings >>= fun _ ->
              return hm
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
            aux (iv = 0) (arity 0 f - iv - 1) >>= fun _ ->
            return hm
        | _ ->
            raise (UnsupportedAction a)
        end
    | `AElim id ->
        let name = UidMap.find id hm in
        let hyp = Utils.get_hyp goal id in
        let mk_destruct2
            (mk_ipat : Names.variable * Names.variable -> Names.variable list list)
            (dest_ipat : Logic_t.intro_pat -> Logic_t.uid * Logic_t.uid)
            : hidmap tactic =
          (* Generate fresh Coq identifiers for destruct *)
          let hyps_names = get_hyps_names coq_goal in
          let name1 = Namegen.next_ident_away name hyps_names in
          let name2 = Namegen.next_ident_away name (Names.Id.Set.add name1 hyps_names) in
          (* Apply destruct *)
          let h = EConstr.mkVar name in
          let pat = mk_or_and_intro_pattern (mk_ipat (name1, name2)) in
          Tactics.destruct false None h (Some pat) None >>= fun _ ->
          (* Retrieve associated Actema identifiers from intro pattern *)
          let id1, id2 = dest_ipat ipat in
          (* Add them to the hidmap *)
          return (UidMap.(hm |> add id1 name1 |> add id2 name2))
        in
        let destruct_and =
          let mk_ipat (x, y) = [[x; y]] in
          let dest_ipat = function
                          | [[id2; id1]] -> id1, id2
                          | _ -> raise (UnexpectedIntroPattern ipat) in
          mk_destruct2 mk_ipat dest_ipat
        in
        let destruct_or =
          let mk_ipat (x, y) = [[x]; [y]] in
          let dest_ipat = function
                          | [[id1]; [id2]] -> id1, id2
                          | _ -> raise (UnexpectedIntroPattern ipat) in
          mk_destruct2 mk_ipat dest_ipat
        in
        begin match hyp.h_form with
        | `FTrue | `FFalse ->
            Tactics.destruct false None (EConstr.mkVar name) None None >>= fun _ ->
            return hm
        | `FConn (`Not, _) ->
            Tactics.simplest_case (EConstr.mkVar name) >>= fun _ ->
            return hm
        | `FConn (`Imp, _) ->
            Tactics.apply (EConstr.mkVar name) >>= fun _ ->
            return hm
        | `FConn (`And, _) | `FConn (`Equiv, _) ->
            destruct_and
        | `FConn (`Or, _) ->
            destruct_or
        | _ ->
            raise (UnsupportedAction a)
        end
    | `ALink (src, dst, itrace) ->
        begin match (src, src.ctxt.kind), (dst, dst.ctxt.kind) with

        (* Forward DnD *)
        | (_, `Hyp), (_, `Hyp) ->
            raise (UnsupportedAction a)

        (* Backward DnD *)
        | (hyp, `Hyp), (concl, `Concl)
        | (concl, `Concl), (hyp, `Hyp) ->
            let h =
              let id = UidMap.find hyp.ctxt.handle hm in
              EConstr.mkVar id in

            let boollist_of_intlist =
              Stdlib.List.map (fun n -> if n = 0 then false else true) in

            let hp =
              hyp.sub |> boollist_of_intlist |> Trm.boollist in
            let gp =
              concl.sub |> boollist_of_intlist |> Trm.boollist in
            
            let t =
              Stdlib.List.(itrace |> split |> fst
                                  |> boollist_of_intlist |> Trm.boollist) in
            
            let i =
              let kname = kername ["Actema"; "DnD"] "empty_inst" in
              EConstr.mkConst (Names.Constant.make1 kname) in

            let open Proofview.Monad in
            calltac "back" [h; hp; gp; t; i] >>= fun _ ->
            return hm

        | _ -> raise UnexpectedDnD
        end
    | _ ->
        raise (UnsupportedAction a)

  let rec proof (hm : hidmap) (t : Logic_t.proof) : unit tactic =
    let open Proofview.Monad in
    match t with
    | `PNode (a, goal, ipat, subs) ->
        Goal.enter begin fun coq_goal ->
          action hm goal coq_goal ipat a >>= fun hm ->
          if subs = [] then 
            Tacticals.tclIDTAC
          else
            let subs_tacs = Stdlib.List.map (proof hm) subs in
            Proofview.tclDISPATCH subs_tacs
        end
end