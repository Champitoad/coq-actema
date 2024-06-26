open Proofview
open Translate
open CoqUtils
open Api

(* -------------------------------------------------------------------- *)
(** The actema tactic *)

type proof = (int * Logic.action) list

(** Export each coq goal to Actema. *)
let export_goals () : Logic.goals tactic =
  let open PVMonad in
  let* coq_goals_tacs = Goal.goals in
  Stdlib.List.fold_right
    begin
      fun coq_goal_tac acc ->
        let* coq_goal = coq_goal_tac in
        let goal, _ = Export.goal coq_goal peano in
        let* goals = acc in
        return (goal :: goals)
    end
    coq_goals_tacs (return [])

let get_user_action (goals : Logic.goals) : Client.action =
  if goals = []
  then begin
    Lwt_main.run (Client.send_qed ());
    Client.Done
  end
  else Lwt_main.run (Client.send_goals goals)

type history = { mutable before : proof; mutable after : proof }

exception ApplyUndo

(** The control flow here is a mess. *)
let interactive_proof () : proof tactic =
  let open PVMonad in
  (* The proof history used to manage Undo/Redo. *)
  let hist = ref { before = []; after = [] } in

  (* At the start of the proof, translate the lemmas to the API format.
     TODO : cache this in a file so that only new/changed lemmas (since the last actema command)
     are translated. *)
  let* lemmas, lemmas_env = Lemmas.export () in

  (* This is the main loop of the plugin, where we handle all actions
     given by the frontend. *)
  let rec aux () =
    let open Client in
    (* Handle Undo/Redo. *)
    let continue idx a =
      let cont =
        let* _ = Actions.execute (idx, a) in
        aux ()
      in
      tclOR cont
        begin
          fun ((exn, _) as iexn) ->
            match exn with
            | ApplyUndo -> aux ()
            | _ ->
                let msg = CErrors.iprint_no_report iexn |> Pp.string_of_ppcmds in
                Lwt_main.run (Client.send_error msg);
                !hist.before <- Stdlib.List.tl !hist.before;
                aux ()
        end
    in

    (* Get the next action that is NOT a lemma request. *)
    let rec handle_lemmas (act : action) : action =
      match act with
      (* We received a lemma request : send the lemmas and get the next action again. *)
      | Lemmas (pattern, term) ->
          (* Pre-select the lemmas. *)
          let lemmas =
            lemmas
            |> Option.default Fun.id (Option.map Lemmas.preselect_name pattern)
            |> Option.default Fun.id (Option.map Lemmas.preselect_selection term)
          in
          (* Send the lemmas to the server. *)
          let act = Lwt_main.run @@ Client.send_lemmas lemmas lemmas_env in
          (* Handle the next action. *)
          handle_lemmas act
      (* Otherwise we are done here. *)
      | _ -> act
    in

    (* Export the goals and get the next action. *)
    let* goals = export_goals () in
    let act = handle_lemmas (get_user_action goals) in
    (* Handle the action. *)
    begin
      match act with
      | Lemmas _ -> failwith "Actema_main.interactive_proof: call handle_lemmas on the action."
      | Do (idx, a) ->
          !hist.before <- (idx, a) :: !hist.before;
          continue idx a
      | Done -> return (Stdlib.List.rev !hist.before)
      | Undo -> begin
          match !hist.before with
          | a :: before ->
              !hist.before <- before;
              !hist.after <- a :: !hist.after;
              tclZERO ApplyUndo
          | [] -> aux ()
        end
      | Redo -> begin
          match !hist.after with
          | (idx, a) :: after ->
              !hist.after <- after;
              !hist.before <- (idx, a) :: !hist.before;
              continue idx a
          | [] -> aux ()
        end
    end
  in

  aux ()

let actema_tac ?(force = false) (action_name : string) : unit tactic =
  let open PVMonad in
  Goal.enter
    begin
      fun coq_goal ->
        let goal, _ = Export.goal coq_goal peano in
        let id = (action_name, (goal.g_hyps, goal.g_concl)) in
        let interactive () =
          let* prf = interactive_proof () in
          Storage.save_proof id prf;
          return ()
        in
        if force
        then interactive ()
        else
          match Storage.load_proof id with
          | Some prf -> Actions.execute_list prf
          | _ -> interactive ()
    end

(*let rec print_modpath mpath =
  match mpath with
  | Names.ModPath.MPdot (mpath, label) ->
      print_modpath mpath ^ " DOT " ^ Names.Label.to_string label
  | Names.ModPath.MPfile dirpath ->
      let dirs = List.rev @@ Names.DirPath.repr dirpath in
      "MPfile " ^ Extlib.List.to_string ~sep:"." Names.Id.to_string dirs
  | Names.ModPath.MPbound bid ->
      let _, id, dirpath = Names.MBId.repr bid in
      let dirs = List.rev @@ Names.DirPath.repr dirpath in
      "MPbound "
      ^ Extlib.List.to_string ~sep:"." Names.Id.to_string dirs
      ^ " " ^ Names.Id.to_string id*)

let isReflexiveInstance goal (cname, (cbody, _)) =
  let sigma = Goal.sigma goal in
  let ty = EConstr.of_constr cbody.Declarations.const_type in
  if EConstr.isApp sigma ty
  then
    let head, args = EConstr.destApp sigma ty in
    if EConstr.isConst sigma head
    then
      let name, _ = EConstr.destConst sigma head in
      let target =
        Names.Constant.make1 @@ kername [ "Coq"; "Classes"; "RelationClasses" ] "Reflexive"
      in
      Names.Constant.UserOrd.equal name target
    else false
  else false

let print_instance goal (inst : Typeclasses.instance) : unit =
  let body =
    match inst.is_impl with
    | Names.GlobRef.ConstRef name -> Environ.lookup_constant name (Goal.env goal)
    | _ ->
        failwith
        @@ Format.sprintf "%s is not a constant !"
             (Pp.string_of_ppcmds @@ Names.GlobRef.print inst.is_impl)
  in
  Log.printf "Instance {\n  class = %s\n  impl = %s\n  body = %s\n}"
    (Pp.string_of_ppcmds @@ Names.GlobRef.print inst.is_class)
    (Pp.string_of_ppcmds @@ Names.GlobRef.print inst.is_impl)
    (Pp.string_of_ppcmds @@ Constr.debug_print body.const_type)

let test_tac () : unit tactic =
  (*Goal.enter
    begin
      fun goal ->
        let env_constants = (Environ.Globals.view (Goal.env goal).env_globals).constants in
        let constants =
          List.filter (isReflexiveInstance goal) (Names.Cmap_env.bindings env_constants)
        in
        (* Log info about the constants. *)
        List.iter
          begin
            fun (cname, (cbody, _)) ->
              let ty = cbody.Declarations.const_type in
              Log.printf "\nFound constant %s :\n" (Names.Constant.to_string cname);
              Log.econstr_debug (Goal.sigma goal) (EConstr.of_constr ty)
          end
          constants;
        Tacticals.tclIDTAC
    end*)
  Goal.enter
    begin
      fun goal ->
        let target =
          (*Names.Constant.make1 @@ kername [ "Coq"; "Classes"; "RelationClasses" ] "Reflexive"*)
          Names.Constant.make1 @@ kername [ "Coq"; "Classes"; "Morphisms" ] "Proper"
        in
        let instances = Typeclasses.instances @@ Names.GlobRef.ConstRef target in
        begin
          match instances with
          | None -> Log.str "Not a class."
          | Some instances -> List.iter (print_instance goal) instances
        end;
        Tacticals.tclIDTAC
    end
