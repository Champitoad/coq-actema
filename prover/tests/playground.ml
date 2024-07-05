open Utils.Pervasive
open Api
open Lang
open Logic
open Prover
open ProverLogic

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
    { g_env = Env.test_env
    ; g_vars = Vars.empty
    ; g_hyps = hyps
    ; g_concl = concl
    }
  in
  try Proof.init [ { g_id = 0; g_pregoal = pregoal } ]
  with TermUtils.TypingError err ->
    failwith
    @@ Format.sprintf "Typing Error when constructing dummy proof :\n%s\n"
         (TermUtils.show_typeError err)

(* forall ?a ?b ?x1 ... ?xn : Prop, a /\ x1 ... xn /\ ~ b
   =?=
   forall ?c ?y1 ... ?yn : Prop, c /\ y1 ... yn /\ c*)
let test_unif n =
  let fold_and ts =
    List.fold_left
      (fun acc t -> Term.mkApps (Term.mkCst Constants.and_) [ t; acc ])
      (Term.mkCst Constants.true_)
      (List.rev ts)
  in

  let add_binders names body =
    List.fold_left
      (fun acc name -> Term.mkProd (Named name) Term.mkProp acc)
      body (List.rev names)
  in

  let a = Name.make "a" in
  let b = Name.make "b" in
  let c = Name.make "c" in
  let xs = List.rev @@ List.init n (Name.make <<< Format.sprintf "x%d") in
  let ys = List.rev @@ List.init n (Name.make <<< Format.sprintf "y%d") in

  let not_b = Term.mkApp (Term.mkCst Constants.not) (Term.mkBVar n) in
  let elems1 = (Term.mkBVar (n + 1) :: List.init n Term.mkBVar) @ [ not_b ] in
  let elems2 = (Term.mkBVar n :: List.init n Term.mkBVar) @ [ Term.mkBVar n ] in

  let h1 = add_binders (a :: b :: xs) @@ fold_and elems1 in
  let sub1 = List.init (n + 2) (const 1) in

  let h2 = add_binders (c :: ys) @@ fold_and elems2 in
  let sub2 = List.init (n + 1) (const 1) in

  Js_log.printf "TERMS :\n%s\n=?=\n%s"
    (Notation.term_to_string Env.test_env h1)
    (Notation.term_to_string Env.test_env h2);
  let proof = mk_test_proof [ h1; h2 ] (Term.mkCst Constants.true_) in
  let g_id = 0 in
  (* Compute the linkactions. *)
  let start = Sys.time () in
  let subst =
    Link.Pred.unifiable ~new_unif:true () proof
      ( [ Path.make ~kind:(Hyp (mk_hyp_name 0)) ~sub:sub1 g_id ]
      , [ Path.make ~kind:(Hyp (mk_hyp_name 1)) ~sub:sub2 g_id ] )
  in
  let stop = Sys.time () in
  Js_log.printf "%f seconds" (stop -. start);

  match subst with
  | None -> Js_log.printf "FAILED"
  | Some unif_data ->
      Js_log.printf "SUBST :\n%s" (Unif.show_subst unif_data.subst)

let () = test_unif 1
