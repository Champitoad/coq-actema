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
  prf |> List.iter begin fun (subgoalIndex, action) ->
    Printf.fprintf oc "%d\n" subgoalIndex;
    Atdgen_runtime.Util.Biniou.to_channel Logic_b.write_action oc action;
    Printf.fprintf oc "\n"
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
        let subgoalIndex = input_line ic |> int_of_string in
        let action = Atdgen_runtime.Util.Biniou.from_channel Logic_b.read_action ic in
        prf := (subgoalIndex, action) :: !prf
      done
    with End_of_file ->
      close_in ic
    end;
    Some (List.rev !prf)
  end

let sign = Translate.peano

let compile_proof (prf : proof) : unit tactic =
  assert false

let interactive_proof (coq_goal : Goal.t) : proof =
  let sign, goal, hm = Export.goal sign coq_goal in
  let action = Lwt_main.run (Client.action goal) in
  assert false

let actema_tac ?(force = false) (action_name : string) : unit tactic =
  Goal.enter begin fun coq_goal ->
    let _, goal, _ = Export.goal sign coq_goal in
    let id = action_name, (goal.g_hyps, goal.g_concl) in
    let proof =
      match load_proof id with
      | Some prf when not force -> prf
      | _ ->
          let proof = interactive_proof coq_goal in
          save_proof id proof; proof
    in
    compile_proof proof
  end

let test_tac : unit tactic =
  let open EConstr in
  Goal.enter begin fun g ->
    let env, sigma = Goal.(env g, sigma g) in
    Log.econstr env sigma EConstr.(Trm.lambda "x" Trm.unit (mkRel 1));
    Proofview.Monad.return ()
  end