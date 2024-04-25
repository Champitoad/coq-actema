open Prover
open Fo
open Utils
open CoreLogic

let tnat = TVar ("nat", 0)
let tbool = TVar ("bool", 0)

let fake_env : env =
  { env_prp =
      Map.of_seq @@ List.to_seq
      @@ [ ("lt", [ tnat; tnat ]); ("gt", [ tnat; tnat ]); ("andb", [ tbool; tbool ]) ]
  ; env_fun =
      Map.of_seq @@ List.to_seq
      @@ [ ("Z", ([], tnat))
         ; ("S", ([ tnat ], tnat))
         ; ("true", ([ tbool ], tbool))
         ; ("true", ([ tbool ], tbool))
         ]
  ; env_prp_name = Map.empty
  ; env_fun_name = Map.empty
  ; env_sort_name = Map.of_seq @@ List.to_seq @@ [ ("nat", "nat"); ("bool", "bool") ]
  ; env_tvar = Map.empty
  ; env_var = Map.empty
  ; env_evar = Map.empty
  ; env_handles = BiMap.empty
  }

let fake_concl : Fo.form =
  FBind (`Forall, "n", tnat, FPred ("lt", [ EFun ("Z", []); EVar ("n", 0) ]))

let fake_pregoal : Proof.pregoal =
  Proof.{ g_env = fake_env; g_hyps = Hyps.empty; g_goal = fake_concl }

let fake_proof = Proof.ginit Hidmap.empty [ fake_pregoal ]

(**********************************************************************************************)
(** Tests *)

let check_actions (actions : Actions.aoutput list) (pred : Actions.aoutput -> bool) : unit =
  if List.exists pred actions
  then ()
  else
    let actions_str = List.to_string ~sep:"\n" ~left:"" ~right:"" Actions.show_aoutput actions in
    Alcotest.failf
      "Failed to find an action matching the given predicate. The list of actions was :\n%s\n"
      actions_str

let test_intro_forall proof =
  let concl_path = IPath.make ~ctxt:{ kind = `Concl; handle = 0 } 0 in
  let source = Actions.{ kind = `Click concl_path; selection = [] } in
  check_actions (Actions.actions fake_proof source) @@ fun output ->
  output.kind = `Click concl_path && output.goal_handle = Handle.ofint 0 && output.action = `Intro 0

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
