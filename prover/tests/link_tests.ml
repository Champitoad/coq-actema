(** Tests for prover/link.ml. *)
(*
open Prover
open Fo
open Utils
open CoreLogic

(**********************************************************************************************)
(** Making mock proofs. *)

let tnat = TVar ("nat", 0)

(** A list of naturals. *)
let tlist = TVar ("list", 0)

let mk_test_env () : env =
  { env_prp = Map.of_seq @@ List.to_seq @@ [ ("perm", [ tlist; tlist ]) ]
  ; env_fun =
      Map.of_seq @@ List.to_seq
      @@ [ ("Z", ([], tnat))
         ; ("S", ([ tnat ], tnat))
         ; ("add", ([ tnat; tnat ], tnat))
         ; ("nil", ([], tlist))
         ; ("cons", ([ tnat; tlist ], tlist))
         ]
  ; env_prp_name = Map.of_seq @@ List.to_seq @@ [ ("perm", "perm") ]
  ; env_fun_name =
      Map.of_seq @@ List.to_seq
      @@ [ ("Z", "Z")
         ; ("S", "S")
         ; ("add", "add")
         ; ("nil", "nil")
         ; ("cons", "cons")
         ]
  ; env_sort_name =
      Map.of_seq @@ List.to_seq @@ [ ("nat", "nat"); ("list", "list") ]
  ; env_tvar =
      Map.of_seq @@ List.to_seq @@ [ ("nat", [ None ]); ("list", [ None ]) ]
  ; env_var = Map.of_seq @@ List.to_seq @@ [ ("local_x", [ (tnat, None) ]) ]
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
  let pregoal =
    Proof.{ g_env = mk_test_env (); g_hyps = hyps; g_goal = concl }
  in
  Proof.ginit Hidmap.empty [ pregoal ]

(**********************************************************************************************)
(** Testing utilities. *)

let check_linkactions (linkactions : Link.linkaction list)
    (pred : Link.linkaction -> bool) : unit =
  if List.exists pred linkactions
  then ()
  else
    let linkactions_str =
      List.to_string ~sep:"\n\n" ~left:"" ~right:"" Link.show_linkaction
        linkactions
    in
    Alcotest.failf
      "Failed to find a linkaction matching the given predicate. There were %d \
       linkactions generated :\n\
       %s\n"
      (List.length linkactions) linkactions_str

let check_empty (linkactions : Link.linkaction list) : unit =
  if linkactions = []
  then ()
  else
    let linkactions_str =
      List.to_string ~sep:"\n\n" ~left:"" ~right:"" Link.show_linkaction
        linkactions
    in
    Alcotest.failf "There were %d unwanted linkactions generated :\n%s\n"
      (List.length linkactions) linkactions_str

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
  if (Proof.Hyps.byid hyps hyp1_id).h_form != hyp1
     || (Proof.Hyps.byid hyps hyp2_id).h_form != hyp2
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

let link_backward hyp hyp_sub concl concl_sub hlpred : Link.linkaction list =
  (* Make a test proof. *)
  let proof = mk_test_proof [ hyp ] concl in
  let goal_id = List.hd @@ Proof.opened proof in
  let hyps = (Proof.byid proof goal_id).g_hyps in
  let hyp_id = List.hd @@ Proof.Hyps.ids hyps in
  (* Compute the linkactions. *)
  let actions =
    hlpred proof
      ( [ IPath.make
            ~ctxt:{ kind = `Hyp; handle = Handle.toint hyp_id }
            ~sub:hyp_sub (Handle.toint goal_id)
        ]
      , [ IPath.make
            ~ctxt:{ kind = `Concl; handle = 0 }
            ~sub:concl_sub (Handle.toint goal_id)
        ] )
  in
  List.concat_map flatten_linkaction actions

let var name = EVar (name, 0)
let forall name type_ body = FBind (`Forall, name, type_, body)
let exist name type_ body = FBind (`Exist, name, type_, body)
let eq a b = FPred ("_EQ", [ a; b ])

(** Is [name] bound in [subst] ? *)
let subst_contains name subst =
  List.exists (fun (name', _) -> name = name') (Form.Subst.aslist subst)

(** Is [name] bound to an [Sbound _] item in [subst] ? *)
let subst_sbound name subst =
  let item_bound sitem = match sitem with Sflex -> false | Sbound _ -> true in
  List.exists
    (fun (name', sitem) -> name = name' && item_bound sitem)
    (Form.Subst.aslist subst)

(** Is [name] bound to an [Sflex _] item in [subst] ? *)
let subst_sflex name subst =
  let item_flex sitem = match sitem with Sflex -> true | Sbound _ -> false in
  List.exists
    (fun (name', sitem) -> name = name' && item_flex sitem)
    (Form.Subst.aslist subst)

(**********************************************************************************************)
(** Testing [Pred.opposite_pol_formulas]. *)

let test_pol_0 () =
  let hlpred = Link.Pred.(lift opposite_pol_formulas) in
  let hyp = FConn (`Imp, [ FConn (`Not, [ FTrue ]); FFalse ]) in
  let concl =
    forall "n" tnat
    @@ FConn (`And, [ eq (var "local_x") (var "n"); exist "l" tlist FTrue ])
  in
  let actions = link_backward hyp [ 0; 0 ] concl [ 0; 1 ] hlpred in
  check_linkactions actions @@ function `Nothing -> true | _ -> false

let test_pol_1 () =
  let hlpred = Link.Pred.(lift opposite_pol_formulas) in
  let hyp = FConn (`Equiv, [ FConn (`Not, [ FTrue ]); FFalse ]) in
  let concl =
    forall "n" tnat
    @@ FConn (`And, [ eq (var "local_x") (var "n"); exist "l" tlist FTrue ])
  in
  let actions = link_backward hyp [ 0; 0 ] concl [ 0; 1 ] hlpred in
  check_linkactions actions @@ function `Nothing -> true | _ -> false

let test_pol_2 () =
  let hlpred = Link.Pred.(lift opposite_pol_formulas) in
  let hyp = FConn (`Imp, [ FConn (`Not, [ FTrue ]); FFalse ]) in
  let concl =
    forall "n" tnat
    @@ FConn (`And, [ eq (var "local_x") (var "n"); exist "l" tlist FTrue ])
  in
  let actions = link_backward hyp [ 0 ] concl [ 0; 1 ] hlpred in
  (* Both formulas have positive polarity. *)
  check_empty actions

let test_pol_3 () =
  let hlpred = Link.Pred.(lift opposite_pol_formulas) in
  let hyp = FConn (`Imp, [ FConn (`Not, [ FTrue ]); FFalse ]) in
  let concl =
    forall "n" tnat
    @@ FConn (`And, [ eq (var "local_x") (var "n"); exist "l" tlist FTrue ])
  in
  let actions = link_backward hyp [ 0; 0 ] concl [ 0; 0; 1 ] hlpred in
  (* The second path points to an expression (not a formula). *)
  check_empty actions

(**********************************************************************************************)
(** Testing [Pred.neg_eq_operand]. *)

let test_eq_0 () =
  let hlpred = Link.Pred.(lift neg_eq_operand) in
  let hyp =
    FConn
      ( `Imp
      , [ FConn
            ( `Not
            , [ forall "x" tnat @@ exist "y" tnat @@ eq (var "x") (var "y") ] )
        ; FFalse
        ] )
  in
  let concl =
    forall "n" tnat
    @@ FConn
         ( `And
         , [ FConn
               (`Imp, [ eq (var "local_x") (EFun ("S", [ var "n" ])); FFalse ])
           ; exist "l" tlist FTrue
           ] )
  in
  let actions = link_backward hyp [ 0; 0; 0; 0; 0 ] concl [ 0 ] hlpred in
  check_linkactions actions @@ function `Nothing -> true | _ -> false

let test_eq_1 () =
  let hlpred = Link.Pred.(lift neg_eq_operand) in
  let hyp =
    FConn
      ( `Imp
      , [ FConn
            ( `Not
            , [ forall "x" tnat @@ exist "y" tnat @@ eq (var "x") (var "y") ] )
        ; FFalse
        ] )
  in
  let concl =
    forall "n" tnat
    @@ FConn
         ( `And
         , [ FConn
               (`Imp, [ eq (var "local_x") (EFun ("S", [ var "n" ])); FFalse ])
           ; exist "l" tlist FTrue
           ] )
  in
  let actions = link_backward hyp [ 1 ] concl [ 0; 0; 0; 1 ] hlpred in
  check_linkactions actions @@ function `Nothing -> true | _ -> false

let test_eq_2 () =
  let hlpred = Link.Pred.(lift neg_eq_operand) in
  let hyp =
    FConn
      ( `Imp
      , [ FConn
            ( `Not
            , [ forall "x" tnat @@ exist "y" tnat @@ eq (var "x") (var "y") ] )
        ; FFalse
        ] )
  in
  let concl =
    forall "n" tnat
    @@ FConn
         ( `And
         , [ FConn
               (`Imp, [ eq (var "local_x") (EFun ("S", [ var "n" ])); FFalse ])
           ; exist "l" tlist FTrue
           ] )
  in
  let actions = link_backward hyp [ 1 ] concl [ 0; 0; 0; 1; 0 ] hlpred in
  (* The second path points too far under an equality. *)
  check_empty actions

let test_eq_3 () =
  let hlpred = Link.Pred.(lift neg_eq_operand) in
  let hyp =
    FConn
      ( `Imp
      , [ FConn
            ( `Not
            , [ forall "x" tnat @@ exist "y" tnat @@ eq (var "x") (var "y") ] )
        ; FFalse
        ] )
  in
  let concl =
    forall "n" tnat
    @@ FConn
         ( `And
         , [ FConn
               (`Imp, [ eq (var "local_x") (EFun ("S", [ var "n" ])); FFalse ])
           ; exist "l" tlist FTrue
           ] )
  in
  let actions = link_backward hyp [ 1 ] concl [ 0; 0; 0 ] hlpred in
  (* The second path points to an equality instead of an equality argument. *)
  check_empty actions

let test_eq_4 () =
  let hlpred = Link.Pred.(lift neg_eq_operand) in
  let hyp1 =
    FConn
      ( `Imp
      , [ FConn
            ( `Not
            , [ forall "x" tnat @@ exist "y" tnat @@ eq (var "x") (var "y") ] )
        ; FFalse
        ] )
  in
  let hyp2 =
    forall "n" tnat
    @@ FConn
         ( `And
         , [ FConn
               (`Imp, [ eq (var "local_x") (EFun ("S", [ var "n" ])); FFalse ])
           ; exist "l" tlist FTrue
           ] )
  in
  let actions = link_forward hyp1 [ 1 ] hyp2 [ 0; 0; 0; 1 ] hlpred in
  (* The second path points to an equality argument with positive polarity. *)
  check_empty actions

(**********************************************************************************************)
(** Testing [Pred.unifiable]. *)

let test_unif_0 () =
  let hlpred = Link.Pred.(lift unifiable) in
  let hyp1 = FConn (`Imp, [ FTrue; FFalse ]) in
  let hyp2 = FTrue in
  let actions = link_forward hyp1 [ 0 ] hyp2 [] hlpred in
  check_linkactions actions @@ function
  | `Subform (s1, s2) -> Form.Subst.is_empty s1 && Form.Subst.is_empty s2
  | _ -> false

let test_unif_1 () =
  let hlpred = Link.Pred.lift Link.Pred.unifiable in
  let hyp =
    forall "l" tlist @@ FPred ("perm", [ EVar ("l", 0); EVar ("l", 0) ])
  in
  let concl =
    forall "x" tnat @@ forall "l" tlist
    @@ FPred
         ( "perm"
         , [ EFun ("cons", [ var "x"; var "l" ])
           ; EFun ("cons", [ var "x"; var "l" ])
           ] )
  in
  let actions = link_backward hyp [ 0 ] concl [ 0; 0 ] hlpred in
  check_linkactions actions @@ function
  | `Subform (s1, s2) -> subst_sbound "l" s1 && Form.Subst.is_empty s2
  | _ -> false

let test_unif_2 () =
  let hlpred = Link.Pred.(lift unifiable) in
  let hyp =
    forall "l1" tlist @@ forall "l2" tlist @@ forall "l3" tlist
    @@ FConn
         ( `Imp
         , [ FPred ("perm", [ var "l1"; var "l2" ])
           ; FConn
               ( `Imp
               , [ FPred ("perm", [ var "l2"; var "l3" ])
                 ; FPred ("perm", [ var "l1"; var "l3" ])
                 ] )
           ] )
  in
  let concl =
    FConn
      ( `Not
      , [ forall "x" tnat @@ exist "l1" tlist @@ forall "l2" tlist
          @@ FPred
               ( "perm"
               , [ EFun ("cons", [ var "x"; var "l1" ])
                 ; EFun ("cons", [ var "x"; var "l2" ])
                 ] )
        ] )
  in
  let actions =
    link_backward hyp [ 0; 0; 0; 1; 1 ] concl [ 0; 0; 0; 0 ] hlpred
  in
  check_linkactions actions @@ function
  | `Subform (s1, s2) ->
      subst_sbound "l1" s1 && subst_sflex "l2" s1 && subst_sbound "l3" s1
      && subst_sflex "x" s2
      && (not (subst_contains "l1" s2))
      && subst_sflex "l2" s2
  | _ -> false

let test_unif_3 () =
  let hlpred = Link.Pred.(lift unifiable) in
  let hyp =
    forall "x" tnat @@ forall "l1" tlist @@ exist "l2" tlist
    @@ FPred
         ( "perm"
         , [ EFun ("cons", [ var "x"; var "l1" ])
           ; EFun ("cons", [ var "x"; var "l2" ])
           ] )
  in
  let concl =
    exist "x" tnat @@ forall "l1" tlist
    @@ FConn
         ( `Not
         , [ forall "l2" tlist @@ forall "l0" tlist
             @@ FConn
                  ( `And
                  , [ FPred
                        ( "perm"
                        , [ EFun ("cons", [ var "x"; var "l1" ]); var "l0" ] )
                    ; FPred
                        ( "perm"
                        , [ var "l0"; EFun ("cons", [ var "x"; var "l2" ]) ] )
                    ] )
           ] )
  in
  let actions =
    link_backward hyp [ 0; 0; 0 ] concl [ 0; 0; 0; 0; 0; 0 ] hlpred
  in
  check_linkactions actions @@ function
  | `Subform (s1, s2) ->
      subst_sbound "x" s1 && subst_sbound "l1" s1
      && (not (subst_contains "l2" s1))
      && subst_sflex "x" s2
      && (not (subst_contains "l1" s2))
      && subst_sflex "l2" s2 && subst_sbound "l0" s2
  | _ -> false

(**********************************************************************************************)
(** Testing [Pred.wf_subform]. *)

let test_sfl_0 () =
  let hlpred = Link.Pred.wf_subform in
  let hyp1 = FConn (`Imp, [ FTrue; FFalse ]) in
  let hyp2 = FTrue in
  let actions = link_forward hyp1 [ 0 ] hyp2 [] hlpred in
  check_linkactions actions @@ function `Subform _ -> true | _ -> false

let test_sfl_1 () =
  let hlpred = Link.Pred.lift Link.Pred.unifiable in
  let hyp =
    forall "l" tlist @@ FPred ("perm", [ EVar ("l", 0); EVar ("l", 0) ])
  in
  let concl =
    forall "x" tnat @@ forall "l" tlist
    @@ FPred
         ( "perm"
         , [ EFun ("cons", [ var "x"; var "l" ])
           ; EFun ("cons", [ var "x"; var "l" ])
           ] )
  in
  let actions = link_backward hyp [ 0 ] concl [ 0; 0 ] hlpred in
  check_linkactions actions @@ function `Subform _ -> true | _ -> false

let test_sfl_2 () =
  let hlpred = Link.Pred.wf_subform in
  let hyp =
    forall "l1" tlist @@ forall "l2" tlist @@ forall "l3" tlist
    @@ FConn
         ( `Imp
         , [ FPred ("perm", [ var "l1"; var "l2" ])
           ; FConn
               ( `Imp
               , [ FPred ("perm", [ var "l2"; var "l3" ])
                 ; FPred ("perm", [ var "l1"; var "l3" ])
                 ] )
           ] )
  in
  let concl =
    forall "x" tnat @@ forall "l1" tlist @@ forall "l2" tlist
    @@ FPred
         ( "perm"
         , [ EFun ("cons", [ var "x"; var "l1" ])
           ; EFun ("cons", [ var "x"; var "l2" ])
           ] )
  in
  let actions = link_backward hyp [ 0; 0; 0; 1; 1 ] concl [ 0; 0; 0 ] hlpred in
  check_linkactions actions @@ function `Subform _ -> true | _ -> false

let test_sfl_3 () =
  let hlpred = Link.Pred.wf_subform in
  let hyp =
    forall "x" tnat @@ forall "l1" tlist @@ forall "l2" tlist
    @@ FPred
         ( "perm"
         , [ EFun ("cons", [ var "x"; var "l1" ])
           ; EFun ("cons", [ var "x"; var "l2" ])
           ] )
  in
  let concl =
    forall "x" tnat @@ forall "l1" tlist @@ forall "l2" tlist
    @@ exist "l0" tlist
    @@ FConn
         ( `And
         , [ FPred ("perm", [ EFun ("cons", [ var "x"; var "l1" ]); var "l0" ])
           ; FPred ("perm", [ var "l0"; EFun ("cons", [ var "x"; var "l2" ]) ])
           ] )
  in
  let actions = link_backward hyp [ 0; 0; 0 ] concl [ 0; 0; 0; 0; 0 ] hlpred in
  check_linkactions actions @@ function `Subform _ -> true | _ -> false

let test_sfl_4 () =
  let hlpred = Link.Pred.wf_subform in
  let hyp1 = FConn (`Equiv, [ FTrue; FFalse ]) in
  let hyp2 = FTrue in
  let actions = link_forward hyp1 [ 0 ] hyp2 [] hlpred in
  check_linkactions actions @@ function `Subform _ -> true | _ -> false

(**********************************************************************************************)
(** Testing [Pred.deep_rewrite]. *)

let test_drw_0 () =
  let hlpred =
    let open Link.Pred in
    deep_rewrite
  in
  let zero = EFun ("Z", []) in
  let hyp = forall "x" tnat @@ eq (EFun ("add", [ var "x"; zero ])) (var "x") in
  let concl =
    forall "n" tnat @@ exist "l" tlist
    @@ FPred
         ( "perm"
         , [ EFun ("cons", [ var "n"; var "l" ])
           ; EFun ("cons", [ EFun ("add", [ var "n"; zero ]); var "l" ])
           ] )
  in
  let actions = link_backward hyp [ 0; 0 ] concl [ 0; 0; 1; 0 ] hlpred in
  check_linkactions actions @@ function `Subform _ -> true | _ -> false

(**********************************************************************************************)
(** Running the tests. *)

let () =
  let open Alcotest in
  let test_group name tests =
    let cases =
      List.mapi
        (fun i t -> test_case (Format.sprintf "%s-%d" name i) `Quick t)
        tests
    in
    (name, cases)
  in
  run "Prover.Link"
    [ test_group "opposite-polarity-formulas"
        [ test_pol_0; test_pol_1; test_pol_2; test_pol_3 ]
    ; test_group "neg-polarity-eq-operand"
        [ test_eq_0; test_eq_1; test_eq_2; test_eq_3; test_eq_4 ]
    ; test_group "unification"
        [ test_unif_0; test_unif_1; test_unif_2; test_unif_3 ]
    ; test_group "subformula-linking"
        [ test_sfl_0; test_sfl_1; test_sfl_2; test_sfl_3; test_sfl_4 ]
    ; test_group "deep-rewrite" [ test_drw_0 ]
    ]
*)
