open Proofview
open Translate
open CoqUtils
open Api

(* -------------------------------------------------------------------- *)
(** The actema tactic *)

type proof = (int * Logic.action) list

(** Carry out the effects of an action in Coq. *)
let compile_action ((idx, a) : int * Logic.action) : unit tactic =
  Goal.enter
    begin
      fun coq_goal ->
        let goal, sign = Export.goal coq_goal peano in
        Import.action sign goal coq_goal a
    end
  |>
  let idx = idx + 1 in
  tclFOCUS idx idx

let compile_proof (prf : proof) : unit tactic =
  let rec aux prf =
    let open PVMonad in
    begin
      match prf with
      | action :: prf ->
          let* _ = compile_action action in
          aux prf
      | [] -> return ()
    end
  in
  aux prf

(** Export all the lemmas we can translate to actema, 
    along with their environment. *)
let export_lemmas () : (Logic.lemma list * Logic.env) tactic =
  let open PVMonad in
  let* coq_goals_tacs = Goal.goals in
  let* lemmas, sign =
    Stdlib.List.fold_right
      begin
        fun coq_goal_tac acc ->
          let* coq_goal = coq_goal_tac in
          let* lemmas, sign = acc in
          let new_lemmas, new_sign = Export.lemmas coq_goal sign in
          return (new_lemmas @ lemmas, new_sign)
      end
      coq_goals_tacs
      (return ([], peano))
  in
  let env = Export.env_of_varsign (NameMap.empty, sign) in
  return (lemmas, env)

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

(** Do a pre-selection of lemmas, according to a name pattern. *)
let preselect_lemmas_name pattern lemmas =
  let filter lem =
    (* Check that the pattern is an exact substring of the lemma's name.
       The test is case-insensitive. *)
    let user_name = String.lowercase_ascii lem.Logic.l_user in
    let pattern = String.lowercase_ascii pattern in
    try
      ignore (BatString.find user_name pattern);
      true
    with Not_found -> false
  in
  List.filter filter lemmas

(** Do a pre-selection of lemmas, according to a selected subterm. *)
let preselect_lemmas_selection selection lemmas = lemmas

exception ApplyUndo

(** The control flow here is a mess. *)
let interactive_proof () : proof tactic =
  let open PVMonad in
  (* The proof history used to manage Undo/Redo. *)
  let hist = ref { before = []; after = [] } in

  (* At the start of the proof, translate the lemmas to the API format.
     TODO : cache this in a file so that only new/changed lemmas (since the last actema command)
     are translated. *)
  let* lemmas, lemmas_env = export_lemmas () in

  (* This is the main loop of the plugin, where we handle all actions
     given by the frontend. *)
  let rec aux () =
    let open Client in
    (* Handle Undo/Redo. *)
    let continue idx a =
      let cont =
        let* _ = compile_action (idx, a) in
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
          (*begin
              match pattern with
              | None -> Log.printf "pattern = None"
              | Some pattern -> Log.printf "pattern = Some %s" pattern
            end;
            begin
              match term with
              | None -> Log.printf "term = None"
              | Some term -> Log.printf "term = Some %s" (Api.Logic.show_term term)
            end;*)
          (* Pre-select the lemmas. *)
          let lemmas =
            lemmas
            |> Option.default Fun.id (Option.map preselect_lemmas_name pattern)
            |> Option.default Fun.id (Option.map preselect_lemmas_selection term)
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
        else match Storage.load_proof id with Some prf -> compile_proof prf | _ -> interactive ()
    end

let rec print_modpath mpath =
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
      ^ " " ^ Names.Id.to_string id

let test_tac () : unit tactic =
  Goal.enter
    begin
      fun coq_goal ->
        let () =
          Environ.fold_constants
            (fun cname cbody acc ->
              if Names.Label.to_string (Names.Constant.label cname) = "target424242"
              then (
                Log.str @@ print_modpath (Names.Constant.modpath cname);
                acc)
              else acc)
            (Goal.env coq_goal) ()
        in
        Tacticals.tclIDTAC
    end
