open Utils.Pervasive
open Api
open Proofview
open CoqUtils
open Translate

exception UnsupportedAction of Logic.action * string
exception UnexpectedDnD
exception InvalidPath of Logic.Path.t

(* -------------------------------------------------------------------- *)
(** * Importing Actema actions as Coq tactics *)

(*let kname = kername [ "Actema"; "HOL" ]
  <
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

    let tdyn_ty () : EConstr.t =
      EConstr.UnsafeMonomorphic.mkInd (Names.MutInd.make1 (kname "TDYN"), 0)

    let tdyn sort =
      let open EConstr in
      let tdyn =
        UnsafeMonomorphic.mkConstruct ((Names.MutInd.make1 (kname "TDYN"), 0), 1)
      in
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
      match ty with
      | Logic.TVar x -> symbol (FOSign.SymbolNames.dnif x sign.symbols)

    let rec expr (sign : FOSign.t) (lenv : Logic.lenv) (e : Logic.expr) : EConstr.t
        =
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

    let rec expr_itrace coq_env (sign : FOSign.t) (env : Logic.env)
        (lenv : Logic.lenv) (side : int) (e : Logic.expr) : EConstr.t =
      match e with
      | Logic.EVar x ->
          if LEnv.exists lenv x
          then begin
            let s =
              sort_index sign (infer_sort (Utils.Vars.push_lenv env lenv) e)
            in
            let index : int = List.(lenv |> split |> fst |> nth_index 0 x) in
            let env_index = if side = 0 then 2 else 1 in
            EConstr.(
              mkApp
                ( mkRel env_index
                , Trm.Datatypes.[| of_nat coq_env s; of_nat coq_env index |] ))
          end
          else Trm.mkVar x
      | Logic.EFun (f, args) ->
          let head = symbol (FOSign.SymbolNames.dnif f sign.symbols) in
          let args = List.map (expr_itrace coq_env sign env lenv side) args in
          EConstr.mkApp (head, Array.of_list args)

    let rec form coq_env sigma (sign : FOSign.t) (env : Logic.env)
        (lenv : Logic.lenv) (f : Logic.form) : EConstr.t =
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
      | Logic.FConn (Logic.And, [ f1; f2 ]) ->
          Trm.Logic.and_ coq_env (form lenv f1) (form lenv f2)
      | Logic.FConn (Logic.Or, [ f1; f2 ]) ->
          Trm.Logic.or_ coq_env (form lenv f1) (form lenv f2)
      | Logic.FConn (Logic.Imp, [ f1; f2 ]) ->
          Trm.Logic.imp (form lenv f1) (form lenv f2)
      | Logic.FConn (Logic.Equiv, [ f1; f2 ]) ->
          Trm.Logic.iff coq_env (form lenv f1) (form lenv f2)
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

    let boollist_of_intlist =
      Stdlib.List.map (fun n -> if n = 0 then false else true)

    let itrace coq_env sigma ts (sign : FOSign.t) (env : Logic.env)
        (mode : [ `Back | `Forw ]) (lp : int list) (rp : int list) (lf : Logic.form)
        (rf : Logic.form) (itr : Logic.itrace) : bool list * EConstr.t =
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
                          then
                            filtered_quant (acc @ [ step ]) mode subitr lp lf rp rf
                          else filtered_quant acc mode subitr lp lf rp rf
                      | ( Logic.FConn ((Logic.Not | Logic.Imp), _)
                        , (`Forw, _, 0 | `Back, 1, 0) ) ->
                          let mode, (lp, lf, rp, rf) =
                            begin
                              match mode with
                              | `Back -> (`Forw, (lp, lf, rp, rf))
                              | `Forw ->
                                  ( `Back
                                  , if side = 0
                                    then (rp, rf, lp, lf)
                                    else (lp, lf, rp, rf) )
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
                         let s =
                           Trm.Datatypes.of_nat coq_env (sort_index sign ty)
                         in
                         let e =
                           let body =
                             expr_itrace coq_env sign env lenv (1 - side) e
                           in
                           Trm.lambda sigma "env1" (env_ty ts ())
                             (Trm.lambda sigma "env2" (env_ty ts ()) body)
                         in
                         Trm.Specif.existT coq_env sigma "s"
                           (Trm.Datatypes.nat coq_env)
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


    let bool_path coq_env (sub : int list) : EConstr.t =
      let boollist_of_intlist =
        Stdlib.List.map (fun n -> if n = 0 then false else true)
      in
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
      Log.str
      @@ Format.sprintf "%s::%s" (mpath_to_string mpath)
           (Names.Label.to_string label)
*)
(*

  let execute_alink coq_goal sign goal src dst (itr : Logic.itrace) =
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
        | Some (hsub, side), Some (fsub, esub) ->
            Some (false, hsub, side, fsub, esub)
        | _ -> begin
            match (get_eq dst, get_term src) with
            | Some (hsub, side), Some (fsub, esub) ->
                Some (true, hsub, side, fsub, esub)
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
            itrace (Goal.env coq_goal) (Goal.sigma coq_goal) ts sign goal.g_env
              `Forw lp rp lf rf itr
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
                  let id =
                    Goal.fresh_name ~basename:(Names.Id.to_string id2) coq_goal ()
                  in
                  EConstr.mkVar id
                in

                let t =
                  Trm.Datatypes.boollist (Goal.env coq_goal) (t @ [ side ])
                in

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
                  let id =
                    Goal.fresh_name ~basename:(Names.Id.to_string id2) coq_goal ()
                  in
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
      | (hyp, Logic.Hyp), (concl, Logic.Concl)
      | (concl, Logic.Concl), (hyp, Logic.Hyp) ->
          let h =
            let id = Names.Id.of_string hyp.ctxt.handle in
            EConstr.mkVar id
          in

          let t, i =
            let lp = hyp.sub in
            let rp = concl.sub in
            let lf = (Utils.get_hyp goal hyp.ctxt.handle).h_form in
            let rf = goal.g_concl in
            itrace (Goal.env coq_goal) (Goal.sigma coq_goal) ts sign goal.g_env
              `Back lp rp lf rf itr
          in

          begin
            match rewrite_data with
            | Some (_, hsub, side, fsub, esub) ->
                let t =
                  Trm.Datatypes.boollist (Goal.env coq_goal) (t @ [ side ])
                in

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

  let execute_ainstantiate coq_goal sign goal (witness : Logic.expr)
      (target : Logic.ipath) =
    let l = bool_path (Goal.env coq_goal) (target.sub @ [ 0 ]) in
    let s =
      infer_sort goal.Logic.g_env witness
      |> sort_index sign
      |> Trm.Datatypes.of_nat (Goal.env coq_goal)
    in
    let o = expr sign [] witness in
    let ts = sorts (Goal.env coq_goal) sign in

    let tac, args =
      begin
        match target.ctxt.kind with
        (* Forward instantiate *)
        | Logic.Hyp ->
            let id = Names.Id.of_string target.ctxt.handle in
            let h = EConstr.mkVar id in
            let id' =
              Goal.fresh_name ~basename:(Names.Id.to_string id) coq_goal ()
            in
            let h' = EConstr.mkVar id' in
            (kname "inst_hyp", [ ts; l; h; h'; s; o ])
        (* Backward instantiate *)
        | Logic.Concl -> (kname "inst_goal", [ ts; l; s; o ])
        | _ -> raise (InvalidPath target)
      end
    in

    calltac tac args*)

(** Return the kernel name of a tactic defined in [Actema.HOL]. *)
let tactic_kname = kername [ "Actema"; "HOL" ]

(** Make an introduction pattern to introduce named variables.
    If any of the given names is already bound, this will create a fresh name instead. *)
let mk_intro_patterns (names : string list) : Tactypes.intro_patterns =
  let open Tactypes in
  List.map
    (fun name ->
      CAst.make @@ IntroNaming (Namegen.IntroFresh (Names.Id.of_string name)))
    names

(*********************************************************************************)
(** [AIntro] actions. *)
(*********************************************************************************)

(** Execute an [AIntro] action. *)
let execute_aintro (coq_goal : Goal.t) side : unit tactic =
  let open Lang in
  let open Term in
  let api_goal = Export.goal coq_goal in
  match (api_goal.g_concl, side) with
  | Cst true_, 0 when Name.equal true_ Constants.true_ ->
      Tactics.one_constructor 1 Tactypes.NoBindings
  | Prod (_, x, ty, body), 0 when not (Term.contains_loose_bvars body) ->
      let pat = mk_intro_patterns [ "h" ] in
      Tactics.intro_patterns false pat
  | App (_, Cst not_, _), 0 when Name.equal not_ Constants.not ->
      let pat = mk_intro_patterns [ "h" ] in
      Tactics.intro_patterns false pat
  | App (_, Cst and_, _), 0 when Name.equal and_ Constants.and_ ->
      Tactics.split Tactypes.NoBindings
  | App (_, Cst equiv, _), 0 when Name.equal equiv Constants.equiv ->
      Tactics.split Tactypes.NoBindings
  | App (_, Cst or_, _), 0 when Name.equal or_ Constants.or_ ->
      Tactics.left Tactypes.NoBindings
  | App (_, Cst or_, _), 1 when Name.equal or_ Constants.or_ ->
      Tactics.right Tactypes.NoBindings
  | Prod (_, x, _, _), 0 ->
      let pat =
        match x with
        | Anonymous -> mk_intro_patterns [ "x" ]
        | Named name -> mk_intro_patterns [ Name.show name ]
      in
      Tactics.intro_patterns false pat
  | App (_, Cst eq, _), 0 when Name.equal eq Constants.eq ->
      (* Here we are not sure that the two sides of the equality are indeed equal.

         The frontend can only handle syntactic equality : it delegates to the plugin
         the responsability of dealing with non-equal terms.

         We choose to simply ignore an intro action on an equality that is not provable by computation. *)
      Tacticals.tclTRY Tactics.reflexivity
  | _ ->
      let msg =
        "The goal has an invalid head connective/predicate for an introduction."
      in
      raise @@ UnsupportedAction (Logic.AIntro side, msg)

(*********************************************************************************)
(** [AElim] actions. *)
(*********************************************************************************)

(** Execute an [AElim] action. This action eliminates the hypothesis named [hyp_name].
    The hypothesis is cleared and replaced by (possibly several) goals which contain derived hypotheses.
    The integer index is used when eliminating an equality, to decide which way (left/right) to rewrite. *)
let execute_aelim (coq_goal : Goal.t) hyp_name i : unit tactic =
  let open Lang in
  let open Term in
  let api_goal = Export.goal coq_goal in
  let hyp_id = Names.Id.of_string @@ Name.show hyp_name in
  let hyp = Logic.Hyps.by_name api_goal.g_hyps hyp_name in
  match hyp.h_form with
  | Cst c when Name.equal c Constants.true_ || Name.equal c Constants.false_ ->
      let bindings = (EConstr.mkVar hyp_id, Tactypes.NoBindings) in
      Tactics.default_elim false (Some true) bindings
  | App (_, Cst not_, _) when Name.equal not_ Constants.not ->
      let bindings = (EConstr.mkVar hyp_id, Tactypes.NoBindings) in
      Tactics.default_elim false (Some true) bindings
  | Prod (_, x, ty, body) when not (Term.contains_loose_bvars body) ->
      Tactics.apply @@ EConstr.mkVar hyp_id
  | App (_, Cst c, _)
    when Name.equal c Constants.and_ || Name.equal c Constants.equiv ->
      (* First eliminate the hypothesis, then introduce the hypotheses we created. *)
      let bindings = (EConstr.mkVar hyp_id, Tactypes.NoBindings) in
      Tacticals.tclTHENS
        (Tactics.default_elim false (Some true) bindings)
        [ Tactics.intro_patterns false
          @@ mk_intro_patterns [ Name.show hyp_name; Name.show hyp_name ]
        ]
  | App (_, Cst or_, _) when Name.equal or_ Constants.or_ ->
      (* First eliminate the hypothesis, then introduce the hypotheses we created. *)
      let bindings = (EConstr.mkVar hyp_id, Tactypes.NoBindings) in
      Tacticals.tclTHENS
        (Tactics.default_elim false (Some true) bindings)
        [ Tactics.intro_patterns false
          @@ mk_intro_patterns [ Name.show hyp_name ]
        ; Tactics.intro_patterns false
          @@ mk_intro_patterns [ Name.show hyp_name ]
        ]
  | App (_, Cst ex, [ _; Lambda (_, x, _, _) ]) when Name.equal ex Constants.ex
    ->
      (* First eliminate the hypothesis, then introduce the variable and hypothesis we created. *)
      let bindings = (EConstr.mkVar hyp_id, Tactypes.NoBindings) in
      let var_name =
        match x with Anonymous -> "x" | Named name -> Name.show name
      in
      Tacticals.tclTHENS
        (Tactics.default_elim false (Some true) bindings)
        [ Tactics.intro_patterns false
          @@ mk_intro_patterns [ var_name; Name.show hyp_name ]
        ]
  | App (_, Cst eq, [ _; _; _ ]) when Name.equal eq Constants.eq && i = 0 ->
      calltac (tactic_kname "rew_all_left") [ EConstr.mkVar hyp_id ]
  | App (_, Cst eq, [ _; _; _ ]) when Name.equal eq Constants.eq && i = 1 ->
      calltac (tactic_kname "rew_all_right") [ EConstr.mkVar hyp_id ]
  | _ ->
      let msg = "Could not apply elimination action." in
      raise @@ UnsupportedAction (Logic.AElim (hyp_name, i), msg)

(*********************************************************************************)
(** [ALemmaAdd] actions. *)
(*********************************************************************************)

(** Execute an [ALemmaAdd] action. This consists in adding the required lemma as a hypothesis. *)
let execute_alemma_add coq_goal lemma_name =
  (* Get the Coq term that corresponds to the lemma. *)
  let symbol_table = Symbols.all coq_goal in
  let hyp_form =
    match Symbols.Table.find_opt lemma_name symbol_table with
    | Some symbol -> Symbols.to_econstr coq_goal symbol
    | None ->
        raise
        @@ UnsupportedAction
             (ALemmaAdd lemma_name, "This lemma does not exist !")
  in

  (* Add the new hypothesis. *)
  let basename =
    lemma_name |> Name.show |> String.split_on_char '.' |> List.last
  in
  let hyp_name = Names.Name.mk_name @@ Goal.fresh_name ~basename coq_goal () in
  Tactics.pose_proof hyp_name hyp_form

(*********************************************************************************)
(** [ALink] actions. *)
(*********************************************************************************)

(** Abstract an itrace, i.e. replace any FVars by BVars in the instantiation witnesses. *)
let abstract_itrace itrace : Logic.choice list =
  let open Lang in
  (* Compute the de Bruijn index associated to the free variable [fvar].
     The lists [passed1] and [passed2] contain the free variables
     that are bound on each side, the most recently bound variable first. *)
  let fvar_index passed1 passed2 fvar : int =
    match List.index_of fvar passed1 with
    | Some idx -> idx
    | None -> begin
        match List.index_of fvar passed2 with
        | Some idx -> idx + List.length passed1
        | None -> failwith "Actions.abstract_itrace: unbound free variable"
      end
  in
  let rec loop passed1 passed2 = function
    (* Simply descend on a side or another. *)
    | Logic.Side side :: choices, fvars1, fvars2 ->
        Logic.Side side :: loop passed1 passed2 (choices, fvars1, fvars2)
    (* Traverse a binder without instantiating. *)
    | Logic.Binder (Left, None) :: choices, v1 :: fvars1, fvars2 ->
        Logic.Binder (Left, None)
        :: loop (v1 :: passed1) passed2 (choices, fvars1, fvars2)
    | Logic.Binder (Right, None) :: choices, fvars1, v2 :: fvars2 ->
        Logic.Binder (Right, None)
        :: loop passed1 (v2 :: passed2) (choices, fvars1, fvars2)
    (* Traverse a binder with instantiating. *)
    | Logic.Binder (Left, Some witness) :: choices, v1 :: fvars1, fvars2 ->
        (* Abstract the free variables in the witness. *)
        let witness =
          Term.fsubst (Term.mkBVar <<< fvar_index passed1 passed2) witness
        in
        (* Don't add [v1] to [passed1] : [v1] is instantiated,
           and thus is not usable by subsequent witnesses. *)
        Logic.Binder (Left, Some witness)
        :: loop passed1 passed2 (choices, fvars1, fvars2)
    | Logic.Binder (Right, Some witness) :: choices, fvars1, v2 :: fvars2 ->
        (* Abstract the free variables in the witness. *)
        let witness =
          Term.fsubst (Term.mkBVar <<< fvar_index passed1 passed2) witness
        in
        (* Don't add [v2] to [passed2]. *)
        Logic.Binder (Right, Some witness)
        :: loop passed1 passed2 (choices, fvars1, fvars2)
    | _ -> []
  in
  loop [] [] itrace

let execute_alink coq_goal src dst (itrace : Logic.itrace) : unit tactic =
  let _ = abstract_itrace itrace in
  Tacticals.tclIDTAC

(*********************************************************************************)
(** Putting it all together. *)
(*********************************************************************************)

(** [convert_sub term sub] converts the path [sub] (that points inside [term])
    from the actema format to the format that the tactics expect. 
    
    The differences between these two formats are : 
    - In Actema applications are n-ary, whereas the tactics expect applications to
      be binary. For instance when pointing to [x] in [f x y z], in Actema
      we use [[1]] but the tactics expect [[0; 0; 1]]. 
    - In Actema existential quantification [exists x : ty, body] is represented 
      as [App (Cst ex, [ty; Lambda (x, ty, body)])], but the tactics work with first-class 
      existentials. For instance when pointing to [ty] or [body] in [exists x : ty, body],
      in Actema we use [[2; 0]] or [[2; 1]], but the tactics expect [[0]] or [[1]]. *)
let rec convert_sub (term : Lang.Term.t) (sub : int list) : int list =
  match (sub, term) with
  | [], _ -> []
  (* Lambdas and products don't change. *)
  | 0 :: sub, Lambda (_, x, ty, body) | 0 :: sub, Prod (_, x, ty, body) ->
      0 :: convert_sub ty sub
  | 1 :: sub, Lambda (_, x, ty, body) | 1 :: sub, Prod (_, x, ty, body) ->
      1 :: convert_sub body sub
  (* Handle existential quantification. *)
  | 2 :: 0 :: sub, App (_, Cst ex, [ _; Lambda (_, x, ty, body) ])
    when Name.equal ex Lang.Constants.ex ->
      0 :: convert_sub body sub
  | 2 :: 1 :: sub, App (_, Cst ex, [ _; Lambda (_, x, ty, body) ])
    when Name.equal ex Lang.Constants.ex ->
      1 :: convert_sub body sub
  (* Turn n-ary applications to binary applications. *)
  (* One argument. *)
  | 0 :: sub, App (_, f, [ arg ]) -> 0 :: convert_sub f sub
  | 1 :: sub, App (_, f, [ arg ]) -> 1 :: convert_sub arg sub
  (* At least two arguments. *)
  | n :: sub, App (_, f, args) when n = List.length args ->
      1 :: convert_sub (List.last args) sub
  | n :: sub, App (_, f, args) when 0 <= n && n < List.length args ->
      let args = List.remove_at (List.length args - 1) args in
      0 :: convert_sub (Lang.Term.mkApps f args) (n :: sub)
  (* This should not happen. *)
  | _ -> failwith "Actions.convert_sub : invalid path"

(** Turn an actema path into a Coq term that can be fed to tactics. *)
let compile_path coq_goal (path : Logic.Path.t) : EConstr.t =
  let open Logic in
  let api_goal = Export.goal coq_goal in
  let term =
    match path.kind with
    | Concl -> api_goal.g_concl
    | Hyp name -> (Logic.Hyps.by_name api_goal.g_hyps name).h_form
    | _ -> failwith "todo"
  in
  path.sub |> convert_sub term |> Trm.Datatypes.natlist (Goal.env coq_goal)

(** [clear_if_var coq_goal econstr] checks if [econstr] is a local variable, 
    and if so clears it from the goal. *)
let clear_if_var coq_goal econstr : unit tactic =
  if EConstr.isVar (Goal.sigma coq_goal) econstr
  then
    let vname = EConstr.destVar (Goal.sigma coq_goal) econstr in
    Tactics.clear [ vname ]
  else Tacticals.tclIDTAC

let execute_helper (action : Logic.action) (coq_goal : Goal.t) : unit tactic =
  let open PVMonad in
  match action with
  | Logic.AId -> Tacticals.tclIDTAC
  | Logic.ADuplicate hyp_name ->
      let hyp_name = Name.show hyp_name in
      let new_name =
        Goal.fresh_name ~basename:hyp_name coq_goal () |> Names.Name.mk_name
      in
      let hyp = EConstr.mkVar @@ Names.Id.of_string hyp_name in
      Tactics.pose_proof new_name hyp
  | Logic.AClear hyp_name ->
      Tactics.clear [ Names.Id.of_string @@ Name.show hyp_name ]
  | Logic.AExact name ->
      let name = Names.Id.of_string @@ Name.show name in
      Tactics.exact_check (EConstr.mkVar name)
  | Logic.AGeneralize name ->
      let name = Names.Id.of_string @@ Name.show name in
      Generalize.generalize_dep (EConstr.mkVar name)
  | Logic.AIntro side -> execute_aintro coq_goal side
  | Logic.AElim (hyp_name, i) -> execute_aelim coq_goal hyp_name i
  | Logic.ALemmaAdd full_name -> execute_alemma_add coq_goal full_name
  | Logic.ALink (src, dst, itrace) -> execute_alink coq_goal src dst itrace
  | Logic.ASimpl path -> begin
      match path.kind with
      | Hyp name ->
          let id = EConstr.mkVar @@ Names.Id.of_string @@ Name.show name in
          let path = compile_path coq_goal path in
          calltac (tactic_kname "simpl_path_hyp") [ id; path ]
      | Concl ->
          let path = compile_path coq_goal path in
          calltac (tactic_kname "simpl_path") [ path ]
      | VarHead _ | VarBody _ | VarType _ ->
          raise @@ UnsupportedAction (action, "Can't simplify in variable")
    end
  | Logic.ACase term ->
      let symbol_table = Symbols.all coq_goal in
      let coq_term = Import.term coq_goal symbol_table term in
      Induction.destruct false (Some true) coq_term None None
      (* For some reason [Induction.destruct] does not clear [coq_term]. *)
      >> clear_if_var coq_goal coq_term
  | Logic.AInd term ->
      let symbol_table = Symbols.all coq_goal in
      let coq_term = Import.term coq_goal symbol_table term in
      Induction.induction false (Some true) coq_term None None
      (* For some reason [Induction.induction] does not clear [coq_term]. *)
      >> clear_if_var coq_goal coq_term
  | Logic.ACaseIntro n ->
      assert (n >= 0);
      failwith "todo"
  | Logic.AIndIntro n ->
      assert (n >= 0);
      failwith "todo"
(*begin
    match path.kind with
    | VarHead var ->
        let id = EConstr.mkVar @@ Names.Id.of_string @@ Name.show var in
        calltac (tactic_kname "mycase_var") [ id ]
    | Concl ->
        let path = compile_path coq_goal path in
        calltac (tactic_kname "mycase") [ path ]
    | _ -> raise @@ UnsupportedAction (action, "TODO")
  end*)

(* _ ->
    raise
    @@ UnsupportedAction
         (action, "This action type is not supported in the plugin.")*)
(*| Logic.ADef (x, _, e) ->
         let id = Names.Id.of_string x in
         let name = Names.Name.Name id in
         let body = expr sign [] e in
         Tactics.pose_tac name body
     | Logic.ALemma full_name -> execute_alemma coq_goal full_name
     | Logic.ACut f ->
         let id = Goal.fresh_name coq_goal () |> Names.Name.mk_name in
         let form =
           form (Goal.env coq_goal) (Goal.sigma coq_goal) sign goal.g_env [] f
         in
         Tactics.assert_before id form
     | Logic.ALink (src, dst, itr) -> execute_alink coq_goal sign goal src dst itr
     | Logic.AInstantiate (witness, target) ->
         execute_ainstantiate coq_goal sign goal witness target
     | Logic.AInd var_name ->
         let var = EConstr.mkVar @@ Names.Id.of_string var_name in
         Induction.induction false (Some true) var None None
     | Logic.AIndt tgt ->
         let tac_name, args =
           let path = tgt.sub |> Trm.Datatypes.natlist (Goal.env coq_goal) in
           match tgt.ctxt.kind with
           | Logic.Concl -> ("myinduction", [ path ])
           | _ ->
               (* TODO: the COQ tactic [myinduction_hyp] is broken. *)
               raise
               @@ UnsupportedAction
                    ( a
                    , "Logic.AIndt only works in the goal (use Logic.AInd for a \
                       local variable). " )
         in
         calltac (kname tac_name) args
     | Logic.ASimpl tgt | Logic.ARed tgt | Logic.ACase tgt | Logic.APbp tgt ->
         (* TODO: the COQ tactic [mycase_hyp] is broken. *)
         let tac_name =
           match a with
           | Logic.ASimpl _ -> "simpl_path"
           | Logic.ARed _ -> "unfold_path"
           | Logic.APbp _ -> "pbp"
           | Logic.ACase _ -> "mycase"
           | _ -> assert false
         in
         let tac_name, args =
           let path = tgt.sub |> Trm.Datatypes.natlist (Goal.env coq_goal) in
           match tgt.ctxt.kind with
           | Logic.Hyp ->
               let id = Names.Id.of_string tgt.ctxt.handle in
               (tac_name ^ "_hyp", [ EConstr.mkVar id; path ])
           | Logic.Concl -> (tac_name, [ path ])
           | _ -> raise (InvalidPath tgt)
         in
         calltac (kname tac_name) args*)

let execute ((idx, a) : int * Logic.action) : unit tactic =
  tclFOCUS (idx + 1) (idx + 1) @@ Goal.enter @@ execute_helper a
