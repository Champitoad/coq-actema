open Prover
open Fo
open Utils
open CoreLogic

let tnat = TVar ("nat", 0)
let tbool = TVar ("bool", 0)

let mk_test_env () : env =
  { env_prp = Map.of_seq @@ List.to_seq @@ [ ("lt", [ tnat; tnat ]); ("andb", [ tbool; tbool ]) ]
  ; env_fun =
      Map.of_seq @@ List.to_seq
      @@ [ ("Z", ([], tnat))
         ; ("S", ([ tnat ], tnat))
         ; ("true", ([], tbool))
         ; ("false", ([], tbool))
         ]
  ; env_prp_name = Map.of_seq @@ List.to_seq @@ [ ("lt", "lt"); ("andb", "andb") ]
  ; env_fun_name =
      Map.of_seq @@ List.to_seq @@ [ ("Z", "Z"); ("S", "S"); ("true", "true"); ("false", "false") ]
  ; env_sort_name = Map.of_seq @@ List.to_seq @@ [ ("nat", "nat"); ("bool", "bool") ]
  ; env_tvar = Map.of_seq @@ List.to_seq @@ [ ("nat", [ None ]); ("bool", [ None ]) ]
  ; env_var = Map.empty
  ; env_evar = Map.empty
  ; env_handles = BiMap.empty
  }

(** Make a dummy proof with a list of hypothesis formulas and a conclusion formula. 
    These formulas can only used functions/symbols/sorts defined in [mk_test_env ()]. *)
let mk_test_proof (hyps : form list) (concl : form) : Proof.proof =
  let hyps =
    hyps
    |> List.map
         begin
           fun form ->
             let handle = Handle.fresh () in
             (handle, Proof.{ h_gen = 0; h_src = Some handle; h_form = form })
         end
    |> Proof.Hyps.of_list
  in
  let pregoal = Proof.{ g_env = mk_test_env (); g_hyps = hyps; g_goal = concl } in
  Proof.ginit Hidmap.empty [ pregoal ]

(**********************************************************************************************)
(** Tests *)

let check_actions (actions : Actions.aoutput list) (pred : Actions.aoutput -> bool) : unit =
  if List.exists pred actions
  then ()
  else
    let actions_str = List.to_string ~sep:"\n\n" ~left:"" ~right:"" Actions.show_aoutput actions in
    Alcotest.failf
      "Failed to find an action matching the given predicate. The list of actions was :\n%s\n"
      actions_str

(* Test an [`AIntro] action on a goal of the form [forall n, ...]. *)
let test_intro_forall proof =
  (* Make the test proof. *)
  let concl = FBind (`Forall, "n", tnat, FPred ("lt", [ EFun ("Z", []); EVar ("n", 0) ])) in
  let proof = mk_test_proof [] concl in
  (* Make the test action source. *)
  let gid = List.hd @@ Proof.opened proof in
  let concl_path = IPath.make ~ctxt:{ kind = `Concl; handle = 0 } (Handle.toint gid) in
  let source = Actions.{ kind = `Click concl_path; selection = [] } in
  (* Generate the actions. *)
  let actions = Actions.actions proof source in
  (* Check the result. *)
  check_actions actions
    begin
      fun output ->
        output.kind = `Click concl_path && output.goal_handle = gid && output.action = `Intro 0
    end

let () =
  let open Alcotest in
  run "Prover.Actions" [ ("intro-forall", [ test_case "intro-forall" `Quick test_intro_forall ]) ]

(*open Prover

  let fake_env =
    Proof.
      { env_prp = Map.of_list @@ [ "" ]
      ; env_fun : (name, sig_) Map.t (* Functions. *)
      ; env_prp_name : (name, name) Map.t
      ; env_fun_name : (name, name) Map.t
      ; env_sort_name : (name, name) Map.t
      ; env_tvar : (name, type_ option list) Map.t
      ; env_var : (name, bvar list) Map.t
      ; env_evar : (name, type_ list) Map.t
      ; env_handles : (vname, Handle.t) BiMap.t
      }

  let test_lowercase () = Alcotest.(check string) "same string" "hello!" (To_test.lowercase "hELLO!")

  (* Run it *)
  let () =
    let open Alcotest in
    run "Prover.Actions" [ ("string-concat", [ test_case "String mashing" `Quick test_str_concat ]) ]
*)
