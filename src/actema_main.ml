open Proofview
open Translate
open CoqUtils

(* -------------------------------------------------------------------- *)
(** The actema tactic *)

(** Every Actema action must be associated to an identifier, so that it can be
    stored and later retrieved by the proof script for recompilation. It could
    be a simple string, but then this would require an intractable amount of
    name management from the user.

    The simple solution that we choose is to add in the identifier the local
    proof context, that is (a hash of) the hypotheses and conclusion at the
    point where the action is performed. Adding the global environment would be
    too much, since the identifier would break as soon as a new constant is
    added/removed earlier in the development (whether or not it is involved in
    the action).

    One could imagine a more elaborate system where actions in the same local
    context but in different modules/sections/proofs have different identifiers,
    but for now we dispense from such complexity (maybe experience will prove
    that it is necessary in the future).
    *)
type aident = Logic_t.aident

type proof = (int * Logic_t.action) list

let string_of_aident (name, (hyps, concl) : aident) : string =
  let hyps = hyps |>
    Extlib.List.to_string begin fun Logic_t.{ h_form; _ } ->
      Utils.string_of_form h_form
    end in
  let concl = concl |> Utils.string_of_form in
  Printf.sprintf "#%s%s%s" name hyps concl

let string_of_proof (prf : proof) : string =
  Extlib.List.to_string ~sep:"\n" ~left:"PROOF\n" ~right:"\nQED"
  begin fun (idx, action) ->
    Printf.sprintf "%d: %s" idx (Utils.string_of_action action)
  end prf

let hash_of (s : string) : string =
  s |> Sha512.string |> Sha512.to_bin |>
  Base64.encode_string ~alphabet:Base64.uri_safe_alphabet

let hash_of_hyp (hyp : Logic_t.hyp) : string =
  hyp |> Logic_b.string_of_hyp |> hash_of

let hash_of_form (form : Logic_t.form) : string =
  form |> Logic_b.string_of_form |> hash_of

let hash_of_lgoal g =
  g |> Logic_b.string_of_lgoal |> hash_of

let hash_of_aident (id : aident) : string =
  id |> Logic_b.string_of_aident |> hash_of

let proofs_path : string =
  let root_path = Loadpath.find_load_path "." |> Loadpath.physical in
  root_path ^ "/actema.proofs"

let path_of_proof (id : aident) : string =
  Printf.sprintf "%s/%s" proofs_path (hash_of_aident id)

let save_proof (id : aident) (prf : proof) : unit =
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
  let oc = open_out path in
  prf |> List.iter begin fun (idx, action) ->
    let actionb = action |>
      Logic_b.string_of_action |>
      Base64.encode_exn in
    Printf.fprintf oc "%d\n%s\n" idx actionb;
  end;
  close_out oc

let load_proof (id : aident) : proof option =
  let path = path_of_proof id in
  if not (CUnix.file_readable_p path) then
    None
  else begin
    let ic = open_in path in
    let prf : proof ref = ref [] in
    begin try
      while true; do
        let line = input_line ic in
        let idx = line |> int_of_string in

        let line = input_line ic in
        let action = line |>
          Base64.decode_exn |>
          Logic_b.action_of_string in

        prf := (idx, action) :: !prf
      done
    with End_of_file ->
      close_in ic
    end;
    let prf = List.rev !prf in
    (* Log.str (string_of_aident id);
    Log.str (string_of_proof prf); *)
    Some prf
  end

let sign = Translate.peano

let compile_action ((idx, a) : int * Logic_t.action) : unit tactic =
  let open Proofview.Monad in
  Goal.enter begin fun coq_goal ->
    let sign, goal, hm = Export.goal sign coq_goal in
    Import.action sign hm goal coq_goal a
  end |>
  let idx = idx + 1 in
  tclFOCUS idx idx

let compile_proof (prf : proof) : unit tactic =
  let rec aux prf =
    let open Proofview.Monad in
    begin match prf with
    | action :: prf ->
        compile_action action >>= fun _ ->
        aux prf
    | [] ->
        return ()
    end in
  aux prf

let export_goals () : Logic_t.goals tactic =
  let open Proofview.Monad in
  Goal.goals >>= fun coq_goals_tacs ->
  Stdlib.List.fold_right begin fun coq_goal_tac acc ->
      coq_goal_tac >>= fun coq_goal ->
      let _, goal, _ = Export.goal sign coq_goal in
      Log.str (Utils.string_of_goal goal);
      acc >>= fun goals ->
      return (goal :: goals)
  end coq_goals_tacs (return [])

let get_user_action (goals : Logic_t.goals) : Client.action =
  let open Proofview.Monad in
  if goals = [] then begin
    Lwt_main.run (Client.qed ());
    Client.Done
  end else
    Lwt_main.run (Client.action goals)

type history = { mutable before : proof; mutable after : proof }
exception ApplyUndo

let interactive_proof () : proof tactic =
  let hist = ref { before = []; after = [] } in

  let rec aux () =
    let open Proofview.Monad in
    let open Client in

    let continue idx a =
      let cont =
        compile_action (idx, a) >>= fun _ ->
        aux () in
      tclOR cont begin fun (exn, _ as iexn) ->
        match exn with
        | ApplyUndo ->
            aux ()
        | _ ->
            let msg =
              CErrors.iprint_no_report iexn |>
              Pp.string_of_ppcmds in
            Lwt_main.run (Client.error msg);
            !hist.before <- Stdlib.List.tl !hist.before;
            aux ()
      end in

    export_goals () >>= fun goals ->
    begin match get_user_action goals with

    | Do (idx, a) ->
        !hist.before <- (idx, a) :: !hist.before;
        continue idx a

    | Done ->
        return (Stdlib.List.rev !hist.before)

    | Undo ->
        begin match !hist.before with
        | a :: before ->
            !hist.before <- before;
            !hist.after <- a :: !hist.after;
            tclZERO ApplyUndo
        | [] -> aux ()
        end

    | Redo ->
        begin match !hist.after with
        | (idx, a) :: after ->
            !hist.after <- after;
            !hist.before <- (idx, a) :: !hist.before;
            continue idx a
        | [] -> aux ()
        end
    end in

  aux ()

let actema_tac ?(force = false) (action_name : string) : unit tactic =
  let open Proofview.Monad in
  Goal.enter begin fun coq_goal ->
    let _, goal, _ = Export.goal sign coq_goal in
    let id = action_name, (goal.g_hyps, goal.g_concl) in
    let interactive () =
      interactive_proof () >>= fun prf ->
      save_proof id prf;
      return () in
    if force then interactive () else
    match load_proof id with
    | Some prf ->
        compile_proof prf
    | _ ->
        interactive ()
  end

let test_tac : unit tactic =
  let open EConstr in
  Goal.enter begin fun g ->
    let env, evd = Goal.(env g, sigma g) in
    let univs : string list =
      Evd.evar_universe_context evd |> UState.ugraph |>
      UGraph.domain |> Univ.Level.Set.elements |>
      List.map Univ.Level.to_string in
    Log.str Extlib.(List.to_string identity univs);
    Proofview.Monad.return ()
  end
