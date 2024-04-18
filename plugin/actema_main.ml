open Proofview
open Translate
open CoqUtils
open Api

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
type aident = Logic.aident

type proof = (int * Logic.action) list

(*let string_of_aident (name, (hyps, concl) : aident) : string =
  let hyps = hyps |>
    Extlib.List.to_string begin fun Logic.{ h_form; _ } ->
      Utils.string_of_form h_form
    end in
  let concl = concl |> Utils.string_of_form in
  Printf.sprintf "#%s%s%s" name hyps concl*)

(*let string_of_proof (prf : proof) : string =
  Extlib.List.to_string ~sep:"\n" ~left:"PROOF\n" ~right:"\nQED"
  begin fun (idx, action) ->
    Printf.sprintf "%d: %s" idx (Utils.string_of_action action)
  end prf*)

let hash_of (s : string) : string =
  s |> Sha512.string |> Sha512.to_bin |> Base64.encode_string ~alphabet:Base64.uri_safe_alphabet

(*let hash_of_hyp (hyp : Logic.hyp) : string =
    hyp |> Logic_b.string_of_hyp |> hash_of

  let hash_of_form (form : Logic.form) : string =
    form |> Logic_b.string_of_form |> hash_of

  let hash_of_lgoal g =
    g |> Logic_b.string_of_lgoal |> hash_of*)

let hash_of_aident (id : aident) : string = id |> Logic.show_aident |> hash_of

let proofs_path () : string =
  let root_path = Loadpath.find_load_path "." |> Loadpath.physical in
  root_path ^ "/actema.proofs"

let path_of_proof (id : aident) : string =
  Format.sprintf "%s/%s" (proofs_path ()) (hash_of_aident id)

(* I was a bit lazy here in using Marshal to save proofs.
   A better solution would probably be to use a text format such as
   JSON or Biniou. *)
let save_proof (id : aident) (prf : proof) : unit =
  let path = path_of_proof id in

  if not (CUnix.file_readable_p (proofs_path ()))
  then begin
    let status = CUnix.sys_command "mkdir" [ proofs_path () ] in
    match status with
    | WEXITED 0 -> ()
    | _ ->
        let err_msg = Printf.sprintf "Could not create directory %s" (proofs_path ()) in
        raise (Sys_error err_msg)
  end;
  let oc = open_out path in
  prf
  |> List.iter
       begin
         fun (idx, action) ->
           let actionb = action |> Fun.flip Marshal.to_string [] |> Base64.encode_exn in
           Printf.fprintf oc "%d\n%s\n" idx actionb
       end;
  close_out oc

let load_proof (id : aident) : proof option =
  let path = path_of_proof id in
  if not (CUnix.file_readable_p path)
  then None
  else begin
    let ic = open_in path in
    let prf : proof ref = ref [] in
    begin
      try
        while true do
          let line = input_line ic in
          let idx = line |> int_of_string in

          let line = input_line ic in
          let action : Logic.action = line |> Base64.decode_exn |> Fun.flip Marshal.from_string 0 in

          prf := (idx, action) :: !prf
        done
      with End_of_file -> close_in ic
    end;
    let prf = List.rev !prf in
    (* Log.str (string_of_aident id);
       Log.str (string_of_proof prf); *)
    Some prf
  end

(*let sign = Translate.peano*)

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
      | Lemmas (pattern, form) ->
          begin
            match pattern with
            | None -> Log.printf "pattern = None"
            | Some pattern -> Log.printf "pattern = Some %s" pattern
          end;

          begin
            match form with
            | None -> Log.printf "form = None"
            | Some form -> Log.printf "form = Some %s" (Api.Logic.show_form form)
          end;
          let act = Lwt_main.run @@ Client.send_lemmas lemmas lemmas_env in
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
          save_proof id prf;
          return ()
        in
        if force
        then interactive ()
        else match load_proof id with Some prf -> compile_proof prf | _ -> interactive ()
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
  Log.str @@ proofs_path ();

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
