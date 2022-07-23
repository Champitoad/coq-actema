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
          (name, []) :: env.Fo_t.env_prp
        else
          env.Fo_t.env_prp
      with e when CErrors.is_anomaly e ->
          env.Fo_t.env_prp in
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

module Uid : sig
  include Map.OrderedType

  val fresh : unit -> t
end with type t = Logic_t.uid = struct
  type t = Logic_t.uid
  
  let compare = Int.compare

  let fresh : unit -> t =
    let count = ref (-1) in
    fun () -> incr count; !count
end

module UidMap = Map.Make(Uid)

type hidmap = Names.Id.t UidMap.t

let export_hyps (coq_env : Environ.env) (evd : Evd.evar_map) : Logic_t.hyp list * hidmap =
  Environ.fold_named_context begin fun _ decl (hyps, hm) ->
    let id = Context.Named.Declaration.get_id decl in
    let ty = decl |> Context.Named.Declaration.get_type |> EConstr.of_constr in
    if is_prop coq_env evd ty then
      let h_id = Uid.fresh () in
      let h_form = dest_form ((coq_env, evd), ty) in
      let hyp = Logic_t.{ h_id; h_form } in
      (hyp :: hyps, UidMap.add h_id id hm)
    else
      (hyps, hm)
  end coq_env ~init:([], UidMap.empty)

let export_goal (goal : Goal.t) : Logic_t.goal * hidmap =
  let coq_env = Goal.env goal in
  let evd = Goal.sigma goal in
  let coq_concl = Goal.concl goal in

  let g_env : Logic_t.env =
    export_env coq_env evd in

  let (g_hyps, hm) : Logic_t.hyp list * hidmap =
    export_hyps coq_env evd in

  let g_concl : Logic_t.form =
    dest_form ((coq_env, evd), coq_concl) in
  
  Logic_t.{ g_env; g_hyps; g_concl }, hm

(* -------------------------------------------------------------------- *)
(** Importing Actema actions as Coq tactics *)

exception UnsupportedAction of Logic_t.action

let import_action (hm : hidmap) (goal : Logic_t.goal) (a : Logic_t.action) : hidmap tactic =
  let open Proofview.Monad in
  match a with
  | `AId ->
      Tacticals.tclIDTAC >>= fun () ->
      return hm
  | `AIntro (i, wit) ->
      Tactics.intro >>= fun () ->
      return hm
  (* | `AElim hd -> *)

  | _ ->
      raise (UnsupportedAction a)

let rec import_proof (hm : hidmap) (t : Logic_t.proof) : unit tactic =
  let open Proofview.Monad in
  match t with
  | `PNode (a, goal, subs) ->
      import_action hm goal a >>= fun hm ->
      if subs = [] then 
        Tacticals.tclIDTAC
      else
        let subs_tacs = Stdlib.List.map (import_proof hm) subs in
        Proofview.tclDISPATCH subs_tacs

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

let path_of_proof ((name, goal) : aident) : string =
  Printf.sprintf "%s/%s-%s" proofs_path (hash_of_goal goal) name

let save_proof (id : aident) (t : Logic_t.proof) : unit =
  let path = path_of_proof id in

  if not (CUnix.file_readable_p proofs_path) then begin
    let status = CUnix.sys_command "mkdir" [proofs_path] in
    match status with
    | WEXITED 0 -> ()
    | _ ->
        let err_msg = Printf.sprintf
          "Could not create directory %s" proofs_path in
        raise (Sys_error err_msg)
  end;
  Atdgen_runtime.Util.Biniou.to_file Logic_b.write_proof path t

let load_proof (id : aident) : Logic_t.proof option =
  let path = path_of_proof id in
  try
    Some (Atdgen_runtime.Util.Biniou.from_file Logic_b.read_proof path)
  with _ ->
    None

let actema_tac (action_name : string) : unit tactic =
  Goal.enter begin fun coq_goal ->
    let goal, hm = export_goal coq_goal in
    Feedback.msg_notice (Pp.str "Goal:");
    Feedback.msg_notice (Pp.str (goal |> Utils.string_of_goal));

    let id = action_name, goal in

    let proof =
      match load_proof id with
      | None ->
          let proof = Lwt_main.run (Client.action goal) in
          save_proof id proof; proof
      | Some t -> t
    in

    Feedback.msg_notice (Pp.str "Proof:");
    Feedback.msg_notice (Pp.str (Utils.string_of_proof proof));
    import_proof hm proof
  end

let actema_force_tac (action_name : string) : unit tactic =
  Goal.enter begin fun coq_goal ->
    let goal, hm = export_goal coq_goal in
    Feedback.msg_notice (Pp.str "Goal:");
    Feedback.msg_notice (Pp.str (goal |> Utils.string_of_goal));

    let id = action_name, goal in

    let proof = Lwt_main.run (Client.action goal) in
    save_proof id proof;

    Feedback.msg_notice (Pp.str "Proof:");
    Feedback.msg_notice (Pp.str (Utils.string_of_proof proof));
    import_proof hm proof
  end
