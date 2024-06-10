open Utils.Pervasive
open Api
open Lang
open Logic
open ProverLogic

(** Compute all the paths in a formula that lead to a subformula in the first order skeleton. *)
let f_subs _env _context f : int list list =
  let rec loop f sub acc =
    let fo = FirstOrder.view _env _context f in
    match fo with
    | FAtom _ -> sub :: acc
    | FConn (conn, args) ->
        List.fold_lefti
          (fun acc i arg -> loop arg ((i + 1) :: sub) acc)
          (sub :: acc) args
    | FImpl (f0, f1) ->
        let acc = sub :: acc in
        let acc = loop f0 (0 :: sub) acc in
        loop f1 (1 :: sub) acc
    | FBind (Forall, x, ty, body) ->
        let acc = sub :: acc in
        let acc = loop ty (0 :: sub) acc in
        loop body (1 :: sub) acc
    | FBind (Exist, x, ty, body) ->
        let acc = sub :: acc in
        let acc = loop ty (1 :: sub) acc in
        loop body (1 :: 2 :: sub) acc
  in
  List.map List.rev @@ loop f [] []

(** Compute all the paths in a formula that lead to the left or right side of an equality
    which is in the first-order skeleton. *)
let eq_subs env context f : int list list =
  let rec loop context f sub acc =
    let fo = FirstOrder.view env context f in
    match fo with
    | FAtom (App (_, Cst eq, [ ty; t1; t2 ])) when Name.equal eq Constants.eq ->
        (2 :: sub) :: (3 :: sub) :: acc
    | FAtom _ -> acc
    | FConn (conn, args) ->
        List.fold_lefti
          (fun acc i arg -> loop context arg ((i + 1) :: sub) acc)
          acc args
    | FImpl (f0, f1) ->
        let acc = loop context f0 (0 :: sub) acc in
        loop context f1 (1 :: sub) acc
    | FBind (Forall, x, ty, body) ->
        let fvar, new_context = Context.add_fresh x ty context in
        let acc = loop context ty (0 :: sub) acc in
        loop new_context (Term.instantiate fvar body) (1 :: sub) acc
    | FBind (Exist, x, ty, body) ->
        let fvar, new_context = Context.add_fresh x ty context in
        let acc = loop context ty (1 :: sub) acc in
        loop new_context (Term.instantiate fvar body) (1 :: 2 :: sub) acc
  in
  List.map List.rev @@ loop context f [] []

module Pred = struct
  type t = Proof.t -> Logic.lemma -> bool

  let true_ _ _ = true
  let false_ _ _ = false
  let and_ p1 p2 proof lemma = p1 proof lemma && p2 proof lemma
  let or_ p1 p2 proof lemma = p1 proof lemma || p2 proof lemma
  let all ps proof lemma = List.for_all (fun p -> p proof lemma) ps
  let any ps proof lemma = List.exists (fun p -> p proof lemma) ps

  let match_name pattern _ lemma =
    (* Check that the pattern is an exact substring of the lemma's name.
       The test is case-insensitive. *)
    let user_name = String.lowercase_ascii @@ Name.show lemma.l_user in
    let pattern = String.lowercase_ascii pattern in
    try
      ignore (String.find user_name pattern);
      true
    with Not_found -> false

  let prepare_goal proof lemma selection : Proof.t * Path.t * Path.t =
    let { g_id; g_pregoal = pregoal } = PathUtils.goal selection proof in
    (* Make a new (pre)goal that has :
       - the lemma as a local hypothesis.
       - its environment extended with the environment of the lemma database. *)
    let new_pregoal =
      let g_hyps =
        Hyps.add pregoal.g_hyps
          { h_name = lemma.l_full; h_form = lemma.l_form; h_gen = 0 }
      in
      let g_env =
        Env.union (Lemmas.env @@ Proof.get_db proof) pregoal.g_env
        (*Lemmas.env @@ Proof.get_db proof*)
      in
      { pregoal with g_hyps; g_env }
    in
    (* Replace the current goal by the new goal. *)
    let new_g_ids, proof = Proof.xprogress proof g_id [ new_pregoal ] in
    let new_g_id = List.hd new_g_ids in
    (* Create a path to the root of the new hypothesis (representing the lemma). *)
    let lemma_path = Path.make ~kind:(Hyp lemma.l_full) new_g_id in
    (* Make sure the path to the selection is in the new goal. *)
    let selection = { selection with goal = new_g_id } in
    (proof, lemma_path, selection)

  let subpath p sub = Path.{ p with sub = p.sub @ sub }

  let link_sfl selection proof lemma =
    (* Create a link predicate for subformula linking. *)
    let hlpred = Link.Pred.wf_subform in
    (* Prepare the goal. *)
    let proof, lemma_path, selection = prepare_goal proof lemma selection in
    let goal = Proof.byid proof lemma_path.goal in
    (* Test against relevant links. As we are testing for subformula linking,
       we only select subpaths of the lemma that lead to a formula. *)
    let subs = f_subs goal.g_env Context.empty lemma.l_form in
    List.exists
      begin
        fun sub ->
          not @@ List.is_empty
          @@ hlpred proof ([ subpath lemma_path sub ], [ selection ])
      end
      subs

  let link_drewrite selection proof lemma =
    (* Create a link predicate for subformula linking. *)
    let hlpred = Link.Pred.deep_rewrite in
    (* Prepare the goal. *)
    let proof, lemma_path, selection = prepare_goal proof lemma selection in
    let goal = Proof.byid proof lemma_path.goal in
    (* Test against relevant links.  As we are testing for deep rewrites,
       we only select subpaths of the lemma that lead to the left or right of an equality.
       This looses a bit of generality as we may miss some links that allow the selection to rewrite in the lemma. *)
    List.exists
      begin
        fun sub ->
          not @@ List.is_empty
          @@ hlpred proof ([ subpath lemma_path sub ], [ selection ])
      end
      (eq_subs goal.g_env Context.empty lemma.l_form)
end

let filter pred proof =
  let old_db = Proof.get_db proof in
  let new_db = Lemmas.filter (fun lemma -> pred proof lemma) old_db in
  Proof.set_db proof new_db
