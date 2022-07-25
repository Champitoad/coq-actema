open Proofview
open Translate

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
    let goal, hm = Export.goal coq_goal in
    let id = action_name, goal in

    let proof =
      match load_proof id with
      | None ->
          let proof = Lwt_main.run (Client.action goal) in
          save_proof id proof; proof
      | Some t -> t
    in

    Import.proof hm proof
  end

let actema_force_tac (action_name : string) : unit tactic =
  Goal.enter begin fun coq_goal ->
    let goal, hm = Export.goal coq_goal in
    let id = action_name, goal in

    let proof = Lwt_main.run (Client.action goal) in
    save_proof id proof;

    Import.proof hm proof
  end
