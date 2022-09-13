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

module E = Export(Peano)
module I = Import(Peano)

let actema_tac (action_name : string) : unit tactic =
  Goal.enter begin fun coq_goal ->
    let goal, hm = E.goal coq_goal in
    let id = action_name, (goal.g_hyps, goal.g_concl) in

    let proof =
      match load_proof id with
      | None ->
          let proof = Lwt_main.run (Client.action goal) in
          save_proof id proof; proof
      | Some t -> t
    in

    I.proof hm proof
  end

let actema_force_tac (action_name : string) : unit tactic =
  Goal.enter begin fun coq_goal ->
    let goal, hm = E.goal coq_goal in
    let id = action_name, (goal.g_hyps, goal.g_concl) in

    let proof = Lwt_main.run (Client.action goal) in
    save_proof id proof;

    I.proof hm proof
  end

let calltac_tac = calltac

let test_tac : unit tactic =
  let open EConstr in
  Goal.enter begin fun g ->
    let env, sigma = Goal.(env g, sigma g) in
    Log.econstr env sigma (Trm.natlist [0;1;2;3;7]);
    Log.econstr env sigma (Trm.boollist [true;false;true]);
    Proofview.Monad.return ()
  end