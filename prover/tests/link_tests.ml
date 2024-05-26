(** Tests for prover/link.ml. *)

open Utils.Pervasive
open Prover
open Api
open Lang
open Logic
open CoreLogic

(**********************************************************************************************)
(** Making mock proofs. *)

let forall name ty body = Term.mkProd (Name.make name) ty body

let exist name ty body =
  Term.(mkApps (mkCst @@ Name.ex) [ ty; mkLambda (Name.make name) ty body ])

let nat : Term.t = Term.mkCst Name.nat
let eq_nat : Term.t = Term.(mkApp (mkCst Name.eq) nat)
let list_nat : Term.t = Term.(mkApp (mkCst @@ Name.make "list") nat)
let perm_nat : Term.t = Term.(mkApp (mkCst @@ Name.make "perm") nat)
let nil_nat : Term.t = Term.(mkApp (mkCst @@ Name.make "nil") nat)
let cons_nat : Term.t = Term.(mkApp (mkCst @@ Name.make "cons") nat)

(** The environment we use for testing in this file.
    It includes the standard [Env.test_env], and lists + permutations. *)
let perm_env =
  let open Term in
  let list0 = mkApp (mkCst @@ Name.make "list") (mkVar 0) in
  Env.test_env
  |> Env.add_constant (Name.make "list") (mkArrow mkType mkType)
  |> Env.add_constant (Name.make "nil") (mkProd (Name.make "A") mkType list0)
  |> Env.add_constant (Name.make "cons")
       (mkProd (Name.make "A") mkType @@ mkArrows [ mkVar 0; list0; list0 ])
  |> Env.add_constant (Name.make "perm")
       (mkProd (Name.make "A") mkType @@ mkArrows [ list0; list0; mkProp ])

let mk_hyp_name i = Name.make @@ Format.sprintf "hyp_%d" i

(** Make a dummy proof with a list of hypothesis formulas and a conclusion formula. *)
let mk_test_proof (hyps : Term.t list) (concl : Term.t) : Proof.t =
  let hyps =
    hyps
    |> List.mapi (fun i form ->
           { h_gen = 0; h_name = mk_hyp_name i; h_form = form })
    |> Hyps.of_list
  in
  let pregoal = { g_env = perm_env; g_hyps = hyps; g_concl = concl } in
  try Proof.init [ { g_id = 0; g_pregoal = pregoal } ]
  with Typing.TypingError err ->
    failwith
    @@ Format.sprintf "Typing Error !!\n%s\n" (Typing.show_typeError err)

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
  | Both (left, right) -> flatten_linkaction left @ flatten_linkaction right
  | _ -> [ la ]

let link_forward hyp1 sub1 hyp2 sub2 hlpred : Link.linkaction list =
  (* Make a test proof. *)
  let proof = mk_test_proof [ hyp1; hyp2 ] (Term.mkCst Name.true_) in
  let g_id = 0 in
  (* Compute the linkactions. *)
  let actions =
    hlpred proof
      ( [ Path.make ~kind:(Hyp (mk_hyp_name 0)) ~sub:sub1 g_id ]
      , [ Path.make ~kind:(Hyp (mk_hyp_name 1)) ~sub:sub2 g_id ] )
  in
  List.concat_map flatten_linkaction actions

let link_backward hyp hyp_sub concl concl_sub hlpred : Link.linkaction list =
  (* Make a test proof. *)
  let proof = mk_test_proof [ hyp ] concl in
  let g_id = 0 in
  (* Compute the linkactions. *)
  let actions =
    hlpred proof
      ( [ Path.make ~kind:(Hyp (mk_hyp_name 0)) ~sub:hyp_sub g_id ]
      , [ Path.make ~kind:Concl ~sub:concl_sub g_id ] )
  in
  List.concat_map flatten_linkaction actions

(** Is [var] bound to an [SFlex] item in [subst] ? *)
let is_flex subst var : bool =
  let open Unif in
  match IntMap.find_opt var subst.mapping with Some SFlex -> true | _ -> false

(** Is [var] bound to an [SRigid] item in [subst] ? *)
let is_rigid subst var : bool =
  let open Unif in
  match IntMap.find_opt var subst.mapping with
  | Some SRigid -> true
  | _ -> false

(** Is [var] bound to an [Sbound _] item in [subst] ? *)
let is_bound subst var =
  let open Unif in
  match IntMap.find_opt var subst.mapping with
  | Some (SBound _) -> true
  | _ -> false

(** Is [var] bound to an [Sbound term] item in [subst] ? *)
let is_bound_to subst var term =
  let open Unif in
  match IntMap.find_opt var subst.mapping with
  | Some (SBound term') when term = term' -> true
  | _ -> false

(**********************************************************************************************)
(** Testing [Pred.opposite_pol_formulas]. *)

let test_pol_0 () =
  let open Term in
  let hlpred = Link.Pred.(lift opposite_pol_formulas) in
  let hyp =
    mkArrow (mkApp (mkCst Name.not) @@ mkCst Name.true_) (mkCst Name.false_)
  in
  let concl =
    forall "n" nat
    @@ mkApps (mkCst Name.and_)
         [ mkApps eq_nat [ mkVar 0; mkVar 0 ]
         ; exist "l" list_nat @@ mkCst Name.true_
         ]
  in
  let actions = link_backward hyp [ 0; 1 ] concl [ 1; 2; 2; 1 ] hlpred in
  check_linkactions actions @@ function Nothing -> true | _ -> false

let test_pol_1 () =
  let open Term in
  let hlpred = Link.Pred.(lift opposite_pol_formulas) in
  let hyp =
    mkApps (mkCst Name.equiv)
      [ mkApp (mkCst Name.not) @@ mkCst Name.true_; mkCst Name.false_ ]
  in
  let concl =
    forall "n" nat
    @@ mkApps (mkCst Name.and_)
         [ mkApps eq_nat [ mkVar 0; mkVar 0 ]
         ; exist "l" list_nat @@ mkCst Name.true_
         ]
  in
  let actions = link_backward hyp [ 1; 1 ] concl [ 1; 2; 2; 1 ] hlpred in
  check_linkactions actions @@ function Nothing -> true | _ -> false

let test_pol_2 () =
  let open Term in
  let hlpred = Link.Pred.(lift opposite_pol_formulas) in
  let hyp =
    mkArrow (mkApp (mkCst Name.not) @@ mkCst Name.true_) (mkCst Name.false_)
  in
  let concl =
    forall "n" nat
    @@ mkApps (mkCst Name.and_)
         [ mkApps eq_nat [ mkVar 0; mkVar 0 ]
         ; exist "l" list_nat @@ mkCst Name.true_
         ]
  in
  let actions = link_backward hyp [ 0 ] concl [ 1; 2; 2; 1 ] hlpred in
  (* Both formulas have positive polarity. *)
  check_empty actions

let test_pol_3 () =
  let open Term in
  let hlpred = Link.Pred.(lift opposite_pol_formulas) in
  let hyp =
    mkArrow (mkApp (mkCst Name.not) @@ mkCst Name.true_) (mkCst Name.false_)
  in
  let concl =
    forall "n" nat
    @@ mkApps (mkCst Name.and_)
         [ mkApps eq_nat [ mkVar 0; mkVar 0 ]
         ; exist "l" list_nat @@ mkCst Name.true_
         ]
  in
  let actions = link_backward hyp [ 0; 1 ] concl [ 1; 1; 2 ] hlpred in
  (* The second path points to an expression (not a formula). *)
  check_empty actions

(**********************************************************************************************)
(** Testing [Pred.neg_eq_operand]. *)

let test_eq_0 () =
  let open Term in
  let hlpred = Link.Pred.(lift neg_eq_operand) in
  let hyp =
    mkArrow
      (mkApp (mkCst Name.not)
      @@ forall "x" nat @@ exist "y" nat
      @@ mkApps eq_nat [ mkVar 1; mkVar 0 ])
      (mkCst Name.false_)
  in
  let concl =
    forall "n" nat
    @@ mkApps (mkCst Name.and_)
         [ mkArrow
             (mkApps eq_nat [ mkVar 0; mkApp (mkCst Name.succ) (mkVar 0) ])
             (mkCst Name.false_)
         ; exist "l" list_nat @@ mkCst Name.true_
         ]
  in
  let actions = link_backward hyp [ 0; 1; 1; 2; 1; 2 ] concl [ 1 ] hlpred in
  check_linkactions actions @@ function Nothing -> true | _ -> false

let test_eq_1 () =
  let open Term in
  let hlpred = Link.Pred.(lift neg_eq_operand) in
  let hyp =
    mkArrow
      (mkApp (mkCst Name.not)
      @@ forall "x" nat @@ exist "y" nat
      @@ mkApps eq_nat [ mkVar 1; mkVar 0 ])
      (mkCst Name.false_)
  in
  let concl =
    forall "n" nat
    @@ mkApps (mkCst Name.and_)
         [ mkArrow
             (mkApps eq_nat [ mkVar 0; mkApp (mkCst Name.succ) (mkVar 0) ])
             (mkCst Name.false_)
         ; exist "l" list_nat @@ mkCst Name.true_
         ]
  in
  let actions = link_backward hyp [ 1 ] concl [ 1; 1; 0; 3 ] hlpred in
  check_linkactions actions @@ function Nothing -> true | _ -> false

let test_eq_2 () =
  let open Term in
  let hlpred = Link.Pred.(lift neg_eq_operand) in
  let hyp =
    mkArrow
      (mkApp (mkCst Name.not)
      @@ forall "x" nat @@ exist "y" nat
      @@ mkApps eq_nat [ mkVar 1; mkVar 0 ])
      (mkCst Name.false_)
  in
  let concl =
    forall "n" nat
    @@ mkApps (mkCst Name.and_)
         [ mkArrow
             (mkApps eq_nat [ mkVar 0; mkApp (mkCst Name.succ) (mkVar 0) ])
             (mkCst Name.false_)
         ; exist "l" list_nat @@ mkCst Name.true_
         ]
  in
  let actions = link_backward hyp [ 1 ] concl [ 1; 1; 0; 3; 1 ] hlpred in
  (* The second path points too far under an equality. *)
  check_empty actions

let test_eq_3 () =
  let open Term in
  let hlpred = Link.Pred.(lift neg_eq_operand) in
  let hyp =
    mkArrow
      (mkApp (mkCst Name.not)
      @@ forall "x" nat @@ exist "y" nat
      @@ mkApps eq_nat [ mkVar 1; mkVar 0 ])
      (mkCst Name.false_)
  in
  let concl =
    forall "n" nat
    @@ mkApps (mkCst Name.and_)
         [ mkArrow
             (mkApps eq_nat [ mkVar 0; mkApp (mkCst Name.succ) (mkVar 0) ])
             (mkCst Name.false_)
         ; exist "l" list_nat @@ mkCst Name.true_
         ]
  in
  let actions = link_backward hyp [ 1 ] concl [ 1; 1; 0 ] hlpred in
  (* The second path points to an equality instead of an equality argument. *)
  check_empty actions

let test_eq_4 () =
  let open Term in
  let hlpred = Link.Pred.(lift neg_eq_operand) in
  let hyp1 =
    mkArrow
      (mkApp (mkCst Name.not)
      @@ forall "x" nat @@ exist "y" nat
      @@ mkApps eq_nat [ mkVar 1; mkVar 0 ])
      (mkCst Name.false_)
  in
  let hyp2 =
    forall "n" nat
    @@ mkApps (mkCst Name.and_)
         [ mkArrow
             (mkApps eq_nat [ mkVar 0; mkApp (mkCst Name.succ) (mkVar 0) ])
             (mkCst Name.false_)
         ; exist "l" list_nat @@ mkCst Name.true_
         ]
  in
  let actions = link_forward hyp1 [ 1 ] hyp2 [ 1; 1; 0; 2 ] hlpred in
  (* The second path points to an equality argument with positive polarity. *)
  check_empty actions

(**********************************************************************************************)
(** Testing [Pred.unifiable]. *)

let test_unif_0 () =
  let open Term in
  let hlpred = Link.Pred.(lift unifiable) in
  let hyp1 = mkArrow (mkCst Name.true_) (mkCst Name.false_) in
  let hyp2 = mkCst Name.true_ in
  let actions = link_forward hyp1 [ 0 ] hyp2 [] hlpred in
  check_linkactions actions @@ function
  | Subform subst ->
      subst.n_free_1 = 0 && subst.n_free_2 = 0
      && IntMap.is_empty subst.mapping
      && Unif.IntGraph.is_empty subst.deps
  | _ -> false

let test_unif_1 () =
  let open Term in
  let hlpred = Link.Pred.lift Link.Pred.unifiable in
  let hyp = forall "l" list_nat @@ mkApps perm_nat [ mkVar 0; mkVar 0 ] in
  let concl =
    forall "x" nat @@ forall "l" list_nat
    @@ mkApps perm_nat
         [ mkApps cons_nat [ mkVar 1; mkVar 0 ]
         ; mkApps cons_nat [ mkVar 1; mkVar 0 ]
         ]
  in
  let actions = link_backward hyp [ 1 ] concl [ 1; 1 ] hlpred in
  check_linkactions actions @@ function
  | Subform subst ->
      subst.n_free_1 = 1 && subst.n_free_2 = 2 && is_bound subst 0
      && is_rigid subst 1 && is_rigid subst 2
  | _ -> false

let test_unif_2 () =
  let open Term in
  let hlpred = Link.Pred.(lift unifiable) in
  let hyp =
    forall "l1" list_nat @@ forall "l2" list_nat @@ forall "l3" list_nat
    @@ mkArrows
         [ mkApps perm_nat [ mkVar 2; mkVar 1 ]
         ; mkApps perm_nat [ mkVar 1; mkVar 0 ]
         ; mkApps perm_nat [ mkVar 2; mkVar 0 ]
         ]
  in
  let concl =
    mkApp (mkCst Name.not)
    @@ forall "x" nat @@ exist "l1" list_nat @@ forall "l2" list_nat
    @@ mkApps perm_nat
         [ mkApps cons_nat [ mkVar 2; mkVar 1 ]
         ; mkApps cons_nat [ mkVar 2; mkVar 0 ]
         ]
  in
  let actions =
    link_backward hyp [ 1; 1; 1; 1; 1 ] concl [ 1; 1; 2; 1; 1 ] hlpred
  in
  check_linkactions actions @@ function
  | Subform subst ->
      subst.n_free_1 = 3 && subst.n_free_2 = 3
      (* In the hypothesis, l1 and l3 are bound but l2 is flex. *)
      && is_bound subst 0
      && is_flex subst 1 && is_bound subst 2
      (* In the conclusion, x and l2 are flex but l1 is rigid. *)
      && is_flex subst 3
      && is_rigid subst 4 && is_flex subst 5
  | _ -> false

let test_unif_3 () =
  let open Term in
  let hlpred = Link.Pred.(lift unifiable) in
  let hyp =
    forall "x" nat @@ forall "l1" list_nat @@ exist "l2" list_nat
    @@ mkApps perm_nat
         [ mkApps cons_nat [ mkVar 2; mkVar 1 ]
         ; mkApps cons_nat [ mkVar 2; mkVar 0 ]
         ]
  in
  let concl =
    exist "x" nat @@ exist "l1" list_nat
    @@ mkApp (mkCst Name.not)
    @@ forall "l2" list_nat @@ forall "l0" list_nat
    @@ mkApps perm_nat [ mkApps cons_nat [ mkVar 3; mkVar 2 ]; mkVar 0 ]
  in
  let actions =
    link_backward hyp [ 1; 1; 2; 1 ] concl [ 2; 1; 2; 1; 1; 1; 1 ] hlpred
  in
  check_linkactions actions @@ function
  | Subform subst ->
      subst.n_free_1 = 3 && subst.n_free_2 = 4
      (* In the hypothesis. *)
      && is_rigid subst 0
      && is_flex subst 1 && is_flex subst 2
      (* In the conclusion. *)
      && is_bound subst 3
      && is_flex subst 4 && is_bound subst 5 && is_bound subst 6
  | _ -> false

(* This is the same as test_unif_3, but we swapped [exist l1] to [forall l1] in the conclusion.
   This has the effect of making [l1] SRigid in the conclusion,
   and it prevents us from finding an acyclic substitution. *)
let test_unif_4 () =
  let open Term in
  let hlpred = Link.Pred.(lift unifiable) in
  let hyp =
    forall "x" nat @@ forall "l1" list_nat @@ exist "l2" list_nat
    @@ mkApps perm_nat
         [ mkApps cons_nat [ mkVar 2; mkVar 1 ]
         ; mkApps cons_nat [ mkVar 2; mkVar 0 ]
         ]
  in
  let concl =
    exist "x" nat @@ forall "l1" list_nat
    @@ mkApp (mkCst Name.not)
    @@ forall "l2" list_nat @@ forall "l0" list_nat
    @@ mkApps perm_nat [ mkApps cons_nat [ mkVar 3; mkVar 2 ]; mkVar 0 ]
  in
  let actions =
    link_backward hyp [ 1; 1; 2; 1 ] concl [ 2; 1; 1; 1; 1; 1 ] hlpred
  in
  check_empty actions

(**********************************************************************************************)
(** Testing [Pred.wf_subform]. *)

(*let test_sfl_0 () =
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
    check_linkactions actions @@ function `Subform _ -> true | _ -> false*)

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
        [ test_unif_0; test_unif_1; test_unif_2; test_unif_3; test_unif_4 ]
      (*; test_group "subformula-linking"
            [ test_sfl_0; test_sfl_1; test_sfl_2; test_sfl_3; test_sfl_4 ]
        ; test_group "deep-rewrite" [ test_drw_0 ]*)
    ]
