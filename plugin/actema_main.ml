open Utils.Pervasive
open Proofview
open CoqUtils
open Api
open Translate

(* -------------------------------------------------------------------- *)
(** The actema tactic *)

type proof = (int * Logic.action) list

(** Export each coq goal to Actema. *)
let export_goals () : Logic.goal list tactic =
  let open PVMonad in
  let* coq_goals = Goal.goals in
  let+ pregoals = mapM (map Export.goal) coq_goals in
  List.mapi (fun i pgoal -> Logic.{ g_id = i; g_pregoal = pgoal }) pregoals

let export_lemmas () : (Logic.lemma list * Lang.Env.t) tactic =
  let open PVMonad in
  let* coq_goals = Goal.goals in
  let+ lemmas, envs = List.split <$> mapM (map Export.lemmas) coq_goals in
  (List.concat lemmas, List.fold Lang.Env.union Lang.Env.empty envs)

let get_user_action (goals : Logic.goal list) : Client.action =
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

  (* At the start of the proof translate the lemmas to the Actema format. *)
  let* lemmas, lemmas_env = export_lemmas () in

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
                let msg =
                  CErrors.iprint_no_report iexn |> Pp.string_of_ppcmds
                in
                Lwt_main.run (Client.send_error msg);
                !hist.before <- Stdlib.List.tl !hist.before;
                aux ()
        end
    in

    (* Get the next action that is NOT a lemma request. *)
    let rec handle_lemmas (act : action) : action =
      match act with
      (* We received a lemma request : send the lemmas and get the next action again. *)
      | Lemmas ->
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
      | Lemmas ->
          Log.error
            "Actema_main.interactive_proof: call handle_lemmas on the action."
      | Do (idx, a) ->
          Log.printf "Received action %d :: %s" idx (Logic.show_action a);
          !hist.before <- (idx, a) :: !hist.before;
          continue idx a
      | Done -> return @@ List.rev !hist.before
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
        let goal = Export.goal coq_goal in
        let id = (action_name, Logic.Hyps.to_list goal.g_hyps, goal.g_concl) in
        let interactive () =
          let* prf = interactive_proof () in
          Storage.save_proof id prf;
          return ()
        in
        if force
        then interactive ()
        else
          match Storage.load_proof id with
          | Some prf -> mapM_ Actions.execute prf
          | _ -> interactive ()
    end

let test_tac () : unit tactic = Tacticals.tclIDTAC
