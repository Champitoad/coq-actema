(** Tests for prover/link.ml. *)

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
         ; ("add", ([ tnat; tnat ], tbool))
         ]
  ; env_prp_name = Map.of_seq @@ List.to_seq @@ [ ("lt", "lt"); ("andb", "andb") ]
  ; env_fun_name =
      Map.of_seq @@ List.to_seq
      @@ [ ("Z", "Z"); ("S", "S"); ("true", "true"); ("false", "false"); ("add", "add") ]
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

let check_linkactions (linkactions : Link.linkaction list) (pred : Link.linkaction -> bool) : unit =
  if List.exists pred linkactions
  then ()
  else
    let linkactions_str =
      List.to_string ~sep:"\n\n" ~left:"" ~right:"" Link.show_linkaction linkactions
    in
    Alcotest.failf
      "Failed to find a linkaction matching the given predicate. There were %d linkactions \
       generated :\n\
       %s\n"
      (List.length linkactions) linkactions_str

(**********************************************************************************************)
(** Actual tests. *)

let rec flatten_linkaction (la : Link.linkaction) : Link.linkaction list =
  match la with
  | `Both (left, right) -> flatten_linkaction left @ flatten_linkaction right
  | _ -> [ la ]

let link_forward hyp1 sub1 hyp2 sub2 hlpred : Link.linkaction list =
  (* Make a test proof. *)
  let proof = mk_test_proof [ hyp1; hyp2 ] FTrue in
  let goal_id = List.hd @@ Proof.opened proof in
  let hyps = (Proof.byid proof goal_id).g_hyps in
  (* Get a handle to each hypothesis and check we didn't swap the handles inadvertently. *)
  let hyp1_id = List.at (Proof.Hyps.ids hyps) 0 in
  let hyp2_id = List.at (Proof.Hyps.ids hyps) 1 in
  if (Proof.Hyps.byid hyps hyp1_id).h_form != hyp1 || (Proof.Hyps.byid hyps hyp2_id).h_form != hyp2
  then Alcotest.failf "Swapped the handles of the two hypotheses !"
  else ();
  (* Compute the linkactions. *)
  let actions =
    hlpred proof
      ( [ IPath.make
            ~ctxt:{ kind = `Hyp; handle = Handle.toint hyp1_id }
            ~sub:sub1 (Handle.toint goal_id)
        ]
      , [ IPath.make
            ~ctxt:{ kind = `Hyp; handle = Handle.toint hyp2_id }
            ~sub:sub2 (Handle.toint goal_id)
        ] )
  in
  List.concat_map flatten_linkaction actions

let test_sfl_1 () =
  let hlpred = Link.Pred.lift Link.Pred.wf_subform in
  let hyp1 = FConn (`Imp, [ FTrue; FFalse ]) in
  let hyp2 = FTrue in
  let actions = link_forward hyp1 [ 0 ] hyp2 [] hlpred in
  check_linkactions actions
    begin
      fun link_act -> match link_act with `Subform _ -> true | _ -> false
    end

let () =
  let open Alcotest in
  run "Prover.Link" [ ("subformula-linking", [ test_case "sfl-1" `Quick test_sfl_1 ]) ]
