(** Tests for prover/link.ml. *)

open Utils.Pervasive
open Prover
open Api
open Lang
open Logic
open ProverLogic

(**********************************************************************************************)
(** Making mock proofs. *)

let forall name ty body = Term.mkProd (Term.Named (Name.make name)) ty body

let exist name ty body =
  Term.(
    mkApps (mkCst @@ Constants.ex)
      [ ty; mkLambda (Term.Named (Name.make name)) ty body ])

let nat : Term.t = Term.mkCst Constants.nat
let eq_nat : Term.t = Term.(mkApp (mkCst Constants.eq) nat)
let list_nat : Term.t = Term.(mkApp (mkCst @@ Name.make "list") nat)
let eq_list_nat : Term.t = Term.(mkApp (mkCst Constants.eq) list_nat)
let perm_nat : Term.t = Term.(mkApp (mkCst @@ Name.make "perm") nat)
let nil_nat : Term.t = Term.(mkApp (mkCst @@ Name.make "nil") nat)
let cons_nat : Term.t = Term.(mkApp (mkCst @@ Name.make "cons") nat)

(** The environment we use for testing in this file.
      It includes the standard [Env.test_env], and lists + permutations. *)
let perm_env =
  let open Term in
  let list0 = mkApp (mkCst @@ Name.make "list") (mkBVar 0) in
  Env.test_env
  |> Env.add_constant (Name.make "list") (mkArrow mkType mkType)
  |> Env.add_constant (Name.make "nil") (forall "A" mkType list0)
  |> Env.add_constant (Name.make "cons")
       (forall "A" mkType @@ mkArrows [ mkBVar 0; list0; list0 ])
  |> Env.add_constant (Name.make "perm")
       (forall "A" mkType @@ mkArrows [ list0; list0; mkProp ])

let mk_hyp_name i = Name.make @@ Format.sprintf "hyp_%d" i

(** Make a dummy proof with a list of hypothesis formulas and a conclusion formula. *)
let mk_test_proof (hyps : Term.t list) (concl : Term.t) : Proof.t =
  let hyps =
    hyps
    |> List.mapi (fun i form ->
           { h_gen = 0; h_name = mk_hyp_name i; h_form = form })
    |> Hyps.of_list
  in
  let pregoal =
    { g_env = perm_env; g_vars = Vars.empty; g_hyps = hyps; g_concl = concl }
  in
  try Proof.init [ { g_id = 0; g_pregoal = pregoal } ]
  with TermUtils.TypingError err ->
    failwith
    @@ Format.sprintf "Typing Error Haha !!\n%s\n"
         (TermUtils.show_typeError err)

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
  let proof = mk_test_proof [ hyp1; hyp2 ] (Term.mkCst Constants.true_) in
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

(**********************************************************************************************)
(** Testing [Pred.opposite_pol_formulas]. *)

let test_pol_0 () =
  let open Term in
  let hlpred = Link.Pred.(lift opposite_pol_formulas) in
  let hyp =
    mkArrow
      (mkApp (mkCst Constants.not) @@ mkCst Constants.true_)
      (mkCst Constants.false_)
  in
  let concl =
    forall "n" nat
    @@ mkApps (mkCst Constants.and_)
         [ mkApps eq_nat [ mkBVar 0; mkBVar 0 ]
         ; exist "l" list_nat @@ mkCst Constants.true_
         ]
  in
  let actions = link_backward hyp [ 0; 1 ] concl [ 1; 2; 2; 1 ] hlpred in
  check_linkactions actions @@ function Nothing -> true | _ -> false

let test_pol_1 () =
  let open Term in
  let hlpred = Link.Pred.(lift opposite_pol_formulas) in
  let hyp =
    mkApps (mkCst Constants.equiv)
      [ mkApp (mkCst Constants.not) @@ mkCst Constants.true_
      ; mkCst Constants.false_
      ]
  in
  let concl =
    forall "n" nat
    @@ mkApps (mkCst Constants.and_)
         [ mkApps eq_nat [ mkBVar 0; mkBVar 0 ]
         ; exist "l" list_nat @@ mkCst Constants.true_
         ]
  in
  let actions = link_backward hyp [ 1; 1 ] concl [ 1; 2; 2; 1 ] hlpred in
  check_linkactions actions @@ function Nothing -> true | _ -> false

let test_pol_2 () =
  let open Term in
  let hlpred = Link.Pred.(lift opposite_pol_formulas) in
  let hyp =
    mkArrow
      (mkApp (mkCst Constants.not) @@ mkCst Constants.true_)
      (mkCst Constants.false_)
  in
  let concl =
    forall "n" nat
    @@ mkApps (mkCst Constants.and_)
         [ mkApps eq_nat [ mkBVar 0; mkBVar 0 ]
         ; exist "l" list_nat @@ mkCst Constants.true_
         ]
  in
  let actions = link_backward hyp [ 0 ] concl [ 1; 2; 2; 1 ] hlpred in
  (* Both formulas have positive polarity. *)
  check_empty actions

let test_pol_3 () =
  let open Term in
  let hlpred = Link.Pred.(lift opposite_pol_formulas) in
  let hyp =
    mkArrow
      (mkApp (mkCst Constants.not) @@ mkCst Constants.true_)
      (mkCst Constants.false_)
  in
  let concl =
    forall "n" nat
    @@ mkApps (mkCst Constants.and_)
         [ mkApps eq_nat [ mkBVar 0; mkBVar 0 ]
         ; exist "l" list_nat @@ mkCst Constants.true_
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
      (mkApp (mkCst Constants.not)
      @@ forall "x" nat @@ exist "y" nat
      @@ mkApps eq_nat [ mkBVar 1; mkBVar 0 ])
      (mkCst Constants.false_)
  in
  let concl =
    forall "n" nat
    @@ mkApps (mkCst Constants.and_)
         [ mkArrow
             (mkApps eq_nat
                [ mkBVar 0; mkApp (mkCst Constants.succ) (mkBVar 0) ])
             (mkCst Constants.false_)
         ; exist "l" list_nat @@ mkCst Constants.true_
         ]
  in
  let actions = link_backward hyp [ 0; 1; 1; 2; 1; 2 ] concl [ 1 ] hlpred in
  check_linkactions actions @@ function Nothing -> true | _ -> false

let test_eq_1 () =
  let open Term in
  let hlpred = Link.Pred.(lift neg_eq_operand) in
  let hyp =
    mkArrow
      (mkApp (mkCst Constants.not)
      @@ forall "x" nat @@ exist "y" nat
      @@ mkApps eq_nat [ mkBVar 1; mkBVar 0 ])
      (mkCst Constants.false_)
  in
  let concl =
    forall "n" nat
    @@ mkApps (mkCst Constants.and_)
         [ mkArrow
             (mkApps eq_nat
                [ mkBVar 0; mkApp (mkCst Constants.succ) (mkBVar 0) ])
             (mkCst Constants.false_)
         ; exist "l" list_nat @@ mkCst Constants.true_
         ]
  in
  let actions = link_backward hyp [ 1 ] concl [ 1; 1; 0; 3 ] hlpred in
  check_linkactions actions @@ function Nothing -> true | _ -> false

let test_eq_2 () =
  let open Term in
  let hlpred = Link.Pred.(lift neg_eq_operand) in
  let hyp =
    mkArrow
      (mkApp (mkCst Constants.not)
      @@ forall "x" nat @@ exist "y" nat
      @@ mkApps eq_nat [ mkBVar 1; mkBVar 0 ])
      (mkCst Constants.false_)
  in
  let concl =
    forall "n" nat
    @@ mkApps (mkCst Constants.and_)
         [ mkArrow
             (mkApps eq_nat
                [ mkBVar 0; mkApp (mkCst Constants.succ) (mkBVar 0) ])
             (mkCst Constants.false_)
         ; exist "l" list_nat @@ mkCst Constants.true_
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
      (mkApp (mkCst Constants.not)
      @@ forall "x" nat @@ exist "y" nat
      @@ mkApps eq_nat [ mkBVar 1; mkBVar 0 ])
      (mkCst Constants.false_)
  in
  let concl =
    forall "n" nat
    @@ mkApps (mkCst Constants.and_)
         [ mkArrow
             (mkApps eq_nat
                [ mkBVar 0; mkApp (mkCst Constants.succ) (mkBVar 0) ])
             (mkCst Constants.false_)
         ; exist "l" list_nat @@ mkCst Constants.true_
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
      (mkApp (mkCst Constants.not)
      @@ forall "x" nat @@ exist "y" nat
      @@ mkApps eq_nat [ mkBVar 1; mkBVar 0 ])
      (mkCst Constants.false_)
  in
  let hyp2 =
    forall "n" nat
    @@ mkApps (mkCst Constants.and_)
         [ mkArrow
             (mkApps eq_nat
                [ mkBVar 0; mkApp (mkCst Constants.succ) (mkBVar 0) ])
             (mkCst Constants.false_)
         ; exist "l" list_nat @@ mkCst Constants.true_
         ]
  in
  let actions = link_forward hyp1 [ 1 ] hyp2 [ 1; 1; 0; 2 ] hlpred in
  (* The second path points to an equality argument with positive polarity. *)
  check_empty actions

(**********************************************************************************************)
(** Testing [Pred.unifiable]. *)

let rec subterm (t : Term.t) sub vars =
  match (t, sub, vars) with
  | _, [], [] -> t
  | App (_, f, args), i :: sub, vars when 0 <= i && i < List.length (f :: args)
    ->
      subterm (List.at (f :: args) i) sub vars
  | Lambda (_, x, ty, body), 0 :: sub, vars
  | Prod (_, x, ty, body), 0 :: sub, vars ->
      subterm ty sub vars
  | Lambda (_, x, ty, body), 1 :: sub, v :: vars
  | Prod (_, x, ty, body), 1 :: sub, v :: vars
    when Term.contains_loose_bvars body ->
      subterm (Term.instantiate v body) sub vars
  | Lambda (_, x, ty, body), 1 :: sub, vars
  | Prod (_, x, ty, body), 1 :: sub, vars ->
      subterm body sub vars
  | _ ->
      failwith
      @@ Format.sprintf "Link_tests.subterm : in term\n%s\nInvalid path %s"
           (Term.show t)
           (List.to_string string_of_int sub)

let check_subform actions (t1, sub1) (t2, sub2) =
  check_linkactions actions @@ function
  | Subform (vars1, vars2, subst) ->
      Term.alpha_equiv
        (Unif.apply subst @@ subterm t1 sub1 vars1)
        (Unif.apply subst @@ subterm t2 sub2 vars2)
  | _ -> false

let test_unif_0 () =
  let open Term in
  let hlpred = Link.Pred.(lift unifiable) in
  let hyp1 = mkArrow (mkCst Constants.true_) (mkCst Constants.false_) in
  let sub1 = [ 0 ] in
  let hyp2 = mkCst Constants.true_ in
  let sub2 = [] in
  let actions = link_forward hyp1 sub1 hyp2 sub2 hlpred in
  check_subform actions (hyp1, sub1) (hyp2, sub2)

let test_unif_1 () =
  let open Term in
  let hlpred = Link.Pred.lift Link.Pred.unifiable in
  let hyp = forall "l" list_nat @@ mkApps perm_nat [ mkBVar 0; mkBVar 0 ] in
  let hyp_sub = [ 1 ] in
  let concl =
    forall "x" nat @@ forall "l" list_nat
    @@ mkApps perm_nat
         [ mkApps cons_nat [ mkBVar 1; mkBVar 0 ]
         ; mkApps cons_nat [ mkBVar 1; mkBVar 0 ]
         ]
  in
  let concl_sub = [ 1; 1 ] in
  let actions = link_backward hyp hyp_sub concl concl_sub hlpred in
  check_subform actions (hyp, hyp_sub) (concl, concl_sub)

let test_unif_2 () =
  let open Term in
  let hlpred = Link.Pred.(lift unifiable) in
  let hyp =
    forall "l1" list_nat @@ forall "l2" list_nat @@ forall "l3" list_nat
    @@ mkArrows
         [ mkApps perm_nat [ mkBVar 2; mkBVar 1 ]
         ; mkApps perm_nat [ mkBVar 1; mkBVar 0 ]
         ; mkApps perm_nat [ mkBVar 2; mkBVar 0 ]
         ]
  in
  let hyp_sub = [ 1; 1; 1; 1; 1 ] in
  let concl =
    mkApp (mkCst Constants.not)
    @@ forall "x" nat @@ exist "l1" list_nat @@ forall "l2" list_nat
    @@ mkApps perm_nat
         [ mkApps cons_nat [ mkBVar 2; mkBVar 1 ]
         ; mkApps cons_nat [ mkBVar 2; mkBVar 0 ]
         ]
  in
  let concl_sub = [ 1; 1; 2; 1; 1 ] in
  let actions = link_backward hyp hyp_sub concl concl_sub hlpred in
  check_subform actions (hyp, hyp_sub) (concl, concl_sub)

let test_unif_3 () =
  let open Term in
  let hlpred = Link.Pred.(lift unifiable) in
  let hyp =
    forall "x" nat @@ forall "l1" list_nat @@ exist "l2" list_nat
    @@ mkApps perm_nat
         [ mkApps cons_nat [ mkBVar 2; mkBVar 1 ]
         ; mkApps cons_nat [ mkBVar 2; mkBVar 0 ]
         ]
  in
  let hyp_sub = [ 1; 1; 2; 1 ] in
  let concl =
    exist "x" nat @@ exist "l1" list_nat
    @@ mkApp (mkCst Constants.not)
    @@ forall "l2" list_nat @@ forall "l0" list_nat
    @@ mkApps perm_nat [ mkApps cons_nat [ mkBVar 3; mkBVar 2 ]; mkBVar 0 ]
  in
  let concl_sub = [ 2; 1; 2; 1; 1; 1; 1 ] in
  let actions = link_backward hyp hyp_sub concl concl_sub hlpred in
  check_subform actions (hyp, hyp_sub) (concl, concl_sub)

(* This is the same as test_unif_3, but we swapped [exist l1] to [forall l1] in the conclusion. *)
let test_unif_4 () =
  let open Term in
  let hlpred = Link.Pred.(lift unifiable) in
  let hyp =
    forall "x" nat @@ forall "l1" list_nat @@ exist "l2" list_nat
    @@ mkApps perm_nat
         [ mkApps cons_nat [ mkBVar 2; mkBVar 1 ]
         ; mkApps cons_nat [ mkBVar 2; mkBVar 0 ]
         ]
  in
  let hyp_sub = [ 1; 1; 2; 1 ] in
  let concl =
    exist "x" nat @@ forall "l1" list_nat
    @@ mkApp (mkCst Constants.not)
    @@ forall "l2" list_nat @@ forall "l0" list_nat
    @@ mkApps perm_nat [ mkApps cons_nat [ mkBVar 3; mkBVar 2 ]; mkBVar 0 ]
  in
  let concl_sub = [ 2; 1; 1; 1; 1; 1 ] in
  let actions = link_backward hyp hyp_sub concl concl_sub hlpred in
  check_subform actions (hyp, hyp_sub) (concl, concl_sub)

let test_unif_5 () =
  let open Term in
  let hlpred = Link.Pred.(lift unifiable) in
  let hyp = forall "x" nat @@ mkApps eq_nat [ mkBVar 0; mkBVar 0 ] in
  let hyp_sub = [ 1; 2 ] in
  let concl = forall "x" nat @@ mkApps eq_nat [ mkBVar 0; mkBVar 0 ] in
  let concl_sub = [ 1; 2 ] in
  let actions = link_backward hyp hyp_sub concl concl_sub hlpred in
  check_subform actions (hyp, hyp_sub) (concl, concl_sub)

let test_unif_6 () =
  let open Term in
  let hlpred = Link.Pred.(lift unifiable) in
  let hyp = forall "x" nat @@ mkApps eq_nat [ mkBVar 0; mkBVar 0 ] in
  let concl =
    forall "x" list_nat @@ mkApps eq_list_nat [ mkBVar 0; mkBVar 0 ]
  in
  let actions = link_backward hyp [ 1; 2 ] concl [ 1; 2 ] hlpred in
  (* The two linked variables are of different types. *)
  check_empty actions

let test_unif_7 () =
  let open Term in
  let hlpred = Link.Pred.(lift unifiable) in
  let hyp =
    forall "A" mkType
    @@ forall "x" (mkBVar 0)
    @@ mkApps (mkCst Constants.eq) [ mkBVar 1; mkBVar 0; mkBVar 0 ]
  in
  let hyp_sub = [ 1; 1; 2 ] in
  let concl =
    forall "B" mkType
    @@ forall "y" (mkBVar 0)
    @@ mkApps (mkCst Constants.eq) [ mkBVar 1; mkBVar 0; mkBVar 0 ]
  in
  let concl_sub = [ 1; 1; 2 ] in
  let actions = link_backward hyp hyp_sub concl concl_sub hlpred in
  check_subform actions (hyp, hyp_sub) (concl, concl_sub)

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
        [ test_unif_0
        ; test_unif_1
        ; test_unif_2
        ; test_unif_3
        ; test_unif_4
        ; test_unif_5
        ; test_unif_6
        ; test_unif_7
        ]
      (*; test_group "subformula-linking"
            [ test_sfl_0; test_sfl_1; test_sfl_2; test_sfl_3; test_sfl_4 ]
        ; test_group "deep-rewrite" [ test_drw_0 ]*)
    ]
