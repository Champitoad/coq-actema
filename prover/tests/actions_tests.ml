open Prover
open Fo
open Utils
open CoreLogic

(**********************************************************************************************)
(** Making mock proofs. *)

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
(** Testing utilities. *)

let check_actions (actions : Actions.aoutput list) (pred : Actions.aoutput -> bool) : unit =
  if List.exists pred actions
  then ()
  else
    let actions_str = List.to_string ~sep:"\n\n" ~left:"" ~right:"" Actions.show_aoutput actions in
    Alcotest.failf
      "Failed to find an action matching the given predicate. There were %d actions generated :\n\
       %s\n"
      (List.length actions) actions_str

(**********************************************************************************************)
(** [`AIntro] tests. *)

(** Make a test to check that an action with action type [`AIntro side] 
    is generated on a goal that has the conclusion [concl]. *)
let mk_intro_test ?(sub = []) concl side =
  (* Make the test proof. *)
  let proof = mk_test_proof [] concl in
  (* Make the test action source. *)
  let gid = List.hd @@ Proof.opened proof in
  let ipath = IPath.make ~ctxt:{ kind = `Concl; handle = 0 } ~sub (Handle.toint gid) in
  let source = Actions.{ kind = `Click ipath; selection = [] } in
  (* Generate the actions. *)
  let actions = Actions.actions proof source in
  (* Check the result. *)
  check_actions actions
    begin
      fun output ->
        output.kind = `Click ipath
        && output.goal_handle = gid
        && output.action = `Intro side
        && output.highlights = [ ipath ] && output.description != ""
    end

(** Test [`AIntro] on [True]. *)
let test_intro_true () =
  let concl = FTrue in
  mk_intro_test concl 0

(** Test [`AIntro] on [not ...]. *)
let test_intro_not () =
  let concl = FConn (`Not, [ FPred ("_EQ", [ EFun ("true", []); EFun ("false", []) ]) ]) in
  mk_intro_test concl 0

(** Test [`AIntro] on [... /\ ...]. *)
let test_intro_and () =
  let concl = FConn (`And, [ FPred ("_EQ", [ EFun ("true", []); EFun ("false", []) ]); FTrue ]) in
  mk_intro_test concl 0

(** Test [`AIntro] on [... <-> ...]. *)
let test_intro_equiv () =
  let concl = FConn (`Equiv, [ FPred ("_EQ", [ EFun ("true", []); EFun ("false", []) ]); FTrue ]) in
  mk_intro_test concl 0

(** Test [`AIntro] on [forall n, ...]. *)
let test_intro_forall () =
  let concl = FBind (`Forall, "n", tnat, FPred ("lt", [ EFun ("Z", []); EVar ("n", 0) ])) in
  mk_intro_test concl 0

(** Test [`AIntro] on [... -> ...]. *)
let test_intro_impl () =
  let concl =
    FConn
      ( `Imp
      , [ FPred ("_EQ", [ EFun ("true", []); EFun ("false", []) ])
        ; FPred ("lt", [ EFun ("Z", []); EFun ("Z", []) ])
        ] )
  in
  mk_intro_test concl 0

(** Test [`AIntro] on [... \/ ...]. *)
let test_intro_or () =
  let concl =
    FConn
      ( `Or
      , [ FPred ("_EQ", [ EFun ("true", []); EFun ("false", []) ]); FConn (`Or, [ FTrue; FFalse ]) ]
      )
  in
  mk_intro_test ~sub:[ 0 ] concl 0;
  mk_intro_test ~sub:[ 1 ] concl 1

(** Test [`AIntro] on [... = ...]. *)
let test_intro_eq () =
  let one = EFun ("S", [ EFun ("Z", []) ]) in
  let two = EFun ("S", [ one ]) in
  let concl = FPred ("_EQ", [ one; two ]) in
  mk_intro_test concl 0

(**********************************************************************************************)
(** [`AElim] tests. *)

(** Make a test to check that an [`AElim] action with action type [action_type] 
    is generated on a goal that has the single hypothesis [hyp]. *)
let mk_elim_test ?(sub = []) hyp side =
  (* Make the test proof. *)
  let proof = mk_test_proof [ hyp ] FTrue in
  (* Make the test action source. *)
  let gid = List.hd @@ Proof.opened proof in
  let hyp_id = List.hd @@ Proof.Hyps.ids (Proof.byid proof gid).g_hyps in
  let ipath =
    IPath.make ~ctxt:{ kind = `Hyp; handle = Handle.toint hyp_id } ~sub (Handle.toint gid)
  in
  let source = Actions.{ kind = `Click ipath; selection = [] } in
  (* Generate the actions. *)
  let actions = Actions.actions proof source in
  (* Check the result. *)
  check_actions actions
    begin
      fun output ->
        output.kind = `Click ipath
        && output.goal_handle = gid
        && output.action = `Elim (hyp_id, side)
        && output.highlights = [ ipath ] && output.description != ""
    end

(** Test [`AElim] on [True]. *)
let test_elim_true () =
  let hyp = FTrue in
  mk_elim_test hyp 0

(** Test [`AElim] on [False]. *)
let test_elim_false () =
  let hyp = FFalse in
  mk_elim_test hyp 0

(** Test [`AElim] on [not ...]. *)
let test_elim_not () =
  let hyp = FConn (`Not, [ FPred ("_EQ", [ EFun ("true", []); EFun ("false", []) ]) ]) in
  mk_elim_test hyp 0

(** Test [`AElim] on [... /\ ...]. *)
let test_elim_and () =
  let hyp = FConn (`And, [ FPred ("_EQ", [ EFun ("true", []); EFun ("false", []) ]); FTrue ]) in
  mk_elim_test hyp 0

(** Test [`AElim] on [... <-> ...]. *)
let test_elim_equiv () =
  let hyp = FConn (`Equiv, [ FPred ("_EQ", [ EFun ("true", []); EFun ("false", []) ]); FTrue ]) in
  mk_elim_test hyp 0

(** Test [`AElim] on [exists n, ...]. *)
let test_elim_exist () =
  let hyp = FBind (`Exist, "n", tnat, FPred ("lt", [ EFun ("Z", []); EVar ("n", 0) ])) in
  mk_elim_test hyp 0

(** Test [`AElim] on [... -> ...]. *)
let test_elim_impl () =
  let hyp =
    FConn
      ( `Imp
      , [ FPred ("_EQ", [ EFun ("true", []); EFun ("false", []) ])
        ; FPred ("lt", [ EFun ("Z", []); EFun ("Z", []) ])
        ] )
  in
  mk_elim_test hyp 0

(** Test [`AElim] on [... \/ ...]. *)
let test_elim_or () =
  let hyp =
    FConn
      ( `Or
      , [ FPred ("_EQ", [ EFun ("true", []); EFun ("false", []) ]); FConn (`Or, [ FTrue; FFalse ]) ]
      )
  in
  mk_elim_test hyp 0

(** Test [`AElim] on [... = ...]. *)
let test_elim_eq () =
  let one = EFun ("S", [ EFun ("Z", []) ]) in
  let two = EFun ("S", [ one ]) in
  let hyp = FPred ("_EQ", [ one; two ]) in
  mk_elim_test hyp ~sub:[ 0 ] 0;
  mk_elim_test hyp ~sub:[ 1 ] 1

let () =
  let open Alcotest in
  run "Prover.Actions"
    [ ( "intro"
      , [ test_case "intro-true" `Quick test_intro_true
        ; test_case "intro-not" `Quick test_intro_not
        ; test_case "intro-and" `Quick test_intro_and
        ; test_case "intro-equiv" `Quick test_intro_equiv
        ; test_case "intro-forall" `Quick test_intro_forall
        ; test_case "intro-impl" `Quick test_intro_impl
        ; test_case "intro-or" `Quick test_intro_or
        ; test_case "intro-eq" `Quick test_intro_eq
        ] )
    ; ( "elim"
      , [ test_case "elim-true" `Quick test_elim_true
        ; test_case "elim-not" `Quick test_elim_not
        ; test_case "elim-and" `Quick test_elim_and
        ; test_case "elim-equiv" `Quick test_elim_equiv
        ; test_case "elim-forall" `Quick test_elim_exist
        ; test_case "elim-impl" `Quick test_elim_impl
        ; test_case "elim-or" `Quick test_elim_or
        ; test_case "elim-eq" `Quick test_elim_eq
        ] )
    ]

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
