open Proofview

(* -------------------------------------------------------------------- *)
(** Exporting Coq goals to Actema *)

let dummy_form : Logic_t.form =
  `FPred ("dummy", [])

type fdest = ((Environ.env * Evd.evar_map) * EConstr.types) -> Logic_t.form

let comp_fdest (d1 : fdest) (d2 : fdest) : fdest = fun (e, t) ->
  try d1 (e, t) with Constr.DestKO -> d2 (e, t)

let ( >>! ) = comp_fdest

let is_prop env evd term =
  let sort = Retyping.get_sort_of env evd term in
  Sorts.is_prop sort

let is_imp (env, evd) x t1 t2 : bool = 
  Printf.printf "%b" (is_prop env evd t1);
  is_prop env evd t1
  && is_prop
       (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (x, t1)) env)
       evd t2
  && (x.Context.binder_name = Names.Anonymous || EConstr.Vars.noccurn evd 1 t2)

let dest_pvar : fdest = fun ((env, evd), t) ->
  if not (is_prop env evd t) then raise Constr.DestKO;
  let name = EConstr.destVar evd t |> Names.Id.to_string in
  `FPred (name, [])

let rec dest_imp : fdest = fun ((_, evd as e), t) ->
  let x, t1, t2 = EConstr.destProd evd t in
  if not (is_imp e x t1 t2) then raise Constr.DestKO;
  `FConn (`Imp, [dest_form (e, t1); dest_form (e, t2)])

and dest_form : fdest = fun et ->
  begin
    dest_pvar >>!
    dest_imp >>!
    fun _ -> dummy_form
  end et

let empty_env : Logic_t.env =
  { env_prp = [("dummy", [])];
    env_fun = [];
    env_var = [];
    env_tvar = [];
    env_handles = [] }

let export_env (coq_env : Environ.env) (evd : Evd.evar_map) : Logic_t.env =
  let add_pvar isprop name env =
    let env_prp =
      try
        if isprop () then
          (name, []) :: env.Logic_t.env_prp
        else
          env.Logic_t.env_prp
      with e when CErrors.is_anomaly e ->
          env.Logic_t.env_prp in
    { env with env_prp } in

  let env = empty_env in

  let env = Environ.fold_constants begin fun c _ env ->
      let isprop () = is_prop coq_env evd (EConstr.mkConst c) in
      let name = Names.Constant.to_string c in
      add_pvar isprop name env
    end coq_env env in

  let env = Environ.fold_named_context begin fun _ decl env ->
      let name = Context.Named.Declaration.get_id decl |> Names.Id.to_string in
      let ty = decl |> Context.Named.Declaration.get_type |> EConstr.of_constr in
      let isprop () = ty |> EConstr.to_constr evd |> Constr.destSort |> Sorts.is_prop in
      add_pvar isprop name env
    end coq_env ~init:env in

  env

let export_hyps (coq_env : Environ.env) (evd : Evd.evar_map) : Logic_t.form list =
  Environ.fold_named_context_reverse begin fun hyps decl ->
    let ty = decl |> Context.Named.Declaration.get_type |> EConstr.of_constr in
    if is_prop coq_env evd ty then
      (dest_form ((coq_env, evd), ty)) :: hyps
    else
      hyps
  end ~init:[] coq_env

let export_goal (goal : Goal.t) : Logic_t.goal =
  let coq_env = Goal.env goal in
  let evd = Goal.sigma goal in
  let coq_concl = Goal.concl goal in

  let env : Logic_t.env =
    export_env coq_env evd in

  let hyps : Logic_t.form list =
    export_hyps coq_env evd in

  let concl : Logic_t.form =
    dest_form ((coq_env, evd), coq_concl) in
  
  env, hyps, concl

let biniou_unhash_dict = Bi_io.make_unhash [
  "EVar"; "EFun";
  "And"; "Or"; "Imp"; "Equiv"; "Not";
  "Forall"; "Exist";
  "FTrue"; "FFalse"; "FPred"; "FConn"; "FBind";
  "F"; "E";
  "Hyp"; "Concl"; "Var"; "Head"; "Body";
  "kind"; "pkind"; "handle";
  "root"; "uid"; "ctxt"; "sub";
  "AId"; "ADef"; "AIntro"; "AElim"; "ACut"; "AAssume"; "AGeneralize"; "AMove"; "ADuplicate"; "ALink";
  "PNode";
  "env_prp"; "env_fun"; "env_var"; "env_tvar"; "env_handles";
]

let string_of_goal goal =
  Bi_io.view ~unhash:biniou_unhash_dict (Logic_b.string_of_goal goal)

let string_of_atree t =
  Bi_io.view ~unhash:biniou_unhash_dict (Logic_b.string_of_atree t)

(* -------------------------------------------------------------------- *)
(** Importing Actema actions as Coq tactics *)

exception UnsupportedAction of Logic_t.action

let import_action (a : Logic_t.action) : unit tactic =
  match a with
  | `AId ->
      Tacticals.tclIDTAC
  | `AIntro (i, wit) ->
      Tactics.intro
  | _ ->
      raise (UnsupportedAction a)

let rec import_atree (t : Logic_t.atree) : unit tactic =
  match t with
  | `PNode (a, subs) ->
      let tac = import_action a in
      if subs = [] then tac
      else
        let subs_tacs = List.map import_atree subs in
        Tacticals.tclTHENS tac subs_tacs

(* -------------------------------------------------------------------- *)
(** The actema tactic *)

(** Action identifier *)
type aident = string * Logic_t.goal

let hash_of_goal (goal : Logic_t.goal) : string =
  goal |> Logic_b.string_of_goal |>
  Sha512.string |> Sha512.to_bin |>
  Base64.encode_string ~alphabet:Base64.uri_safe_alphabet

let proofs_path : string =
  let root_path = Loadpath.find_load_path "." |> Loadpath.physical in
  root_path ^ "/actema.proofs"

let path_of_atree ((name, goal) : aident) : string =
  Printf.sprintf "%s/%s-%s" proofs_path (hash_of_goal goal) name

let save_atree (id : aident) (t : Logic_t.atree) : unit =
  let path = path_of_atree id in

  if not (CUnix.file_readable_p proofs_path) then begin
    let status = CUnix.sys_command "mkdir" [proofs_path] in
    match status with
    | WEXITED 0 -> ()
    | _ ->
        let err_msg = Printf.sprintf
          "Could not create directory %s" proofs_path in
        raise (Sys_error err_msg)
  end;
  Atdgen_runtime.Util.Biniou.to_file Logic_b.write_atree path t

let load_atree (id : aident) : Logic_t.atree option =
  let path = path_of_atree id in
  try
    Some (Atdgen_runtime.Util.Biniou.from_file Logic_b.read_atree path)
  with Sys_error _ ->
    None

let actema_tac (action_name : string) : unit tactic =
  Goal.enter begin fun coq_goal ->
    let goal = export_goal coq_goal in
    Feedback.msg_notice (Pp.str "Goal:");
    Feedback.msg_notice (Pp.str (goal |> string_of_goal));

    let id = action_name, goal in

    let atree =
      match load_atree id with
      | None ->
          let atree = Lwt_main.run (Client.action goal) in
          save_atree id atree; atree
      | Some t -> t
    in

    Feedback.msg_notice (Pp.str "Action tree:");
    Feedback.msg_notice (Pp.str (string_of_atree atree));
    import_atree atree
  end

let actema_force_tac (action_name : string) : unit tactic =
  Goal.enter begin fun coq_goal ->
    let goal = export_goal coq_goal in
    Feedback.msg_notice (Pp.str "Goal:");
    Feedback.msg_notice (Pp.str (goal |> string_of_goal));

    let id = action_name, goal in

    let atree = Lwt_main.run (Client.action goal) in
    save_atree id atree;

    Feedback.msg_notice (Pp.str "Action tree:");
    Feedback.msg_notice (Pp.str (string_of_atree atree));
    import_atree atree
  end