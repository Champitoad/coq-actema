open Utils.Pervasive
open Api
open Lang
open Logic
open ProverLogic

(** Function to test whether two terms [t1] and [t2] are *not* unifiable.
    - If it returns [true] then [t1] and [t2] are *not* unifiable. 
    - If it returns [false] we didn't gain any information. 
    
    For efficiency reasons this function operates directly on de Bruijn syntax 
    instead of locally nameless syntax. *)
let rec not_unifiable_fast depth ((t1, t2) : Term.t * Term.t) : bool =
  match (t1, t2) with
  | FVar _, _ | _, FVar _ ->
      failwith "Link.not_unifiable_fast : unexpected FVar"
  (* A free variable (i.e. a BVar that lives above [depth]) might get unified with anything. *)
  | BVar n, _ when n >= depth -> false
  | _, BVar n when n >= depth -> false
  (* A sort is unifiable only with the same sort. *)
  | Sort s1, Sort s2 when s1 = s2 -> false
  (* A constant is unificable only with the same constant. *)
  | Cst c1, Cst c2 when Name.equal c1 c2 -> false
  (* Recursive cases. *)
  | App (_, f1, args1), App (_, f2, args2)
    when List.length args1 = List.length args2 ->
      List.exists (not_unifiable_fast depth)
      @@ List.combine (f1 :: args1) (f2 :: args2)
  | Lambda (_, x1, ty1, body1), Lambda (_, x2, ty2, body2)
  | Prod (_, x1, ty1, body1), Prod (_, x2, ty2, body2) ->
      not_unifiable_fast depth (ty1, ty2)
      || not_unifiable_fast (depth + 1) (body1, body2)
  (* In every other case [t1] and [t2] are *not* unifiable. *)
  | _ -> true

(** Compute all the paths in a formula that lead to a subformula that :
    - is in the first order skeleton.
    - is possibly unifiable with [target]. *)
let f_subs target f : int list list =
  let rec loop f sub acc =
    (* Get the paths to all subformulas. *)
    let acc =
      let fo = FirstOrder.view Env.empty Context.empty f in
      match fo with
      | FAtom _ -> acc
      | FConn (conn, args) ->
          List.fold_lefti
            (fun acc i arg -> loop arg ((i + 1) :: sub) acc)
            acc args
      | FImpl (f0, f1) ->
          let acc = loop f0 (0 :: sub) acc in
          loop f1 (1 :: sub) acc
      (* For Forall/Exist we don't recurse in the type of the binder. *)
      | FBind (Forall, x, ty, body) -> loop body (1 :: sub) acc
      | FBind (Exist, x, ty, body) -> loop body (1 :: 2 :: sub) acc
    in
    (* Check if [target] and [f] are *not* unifiable. *)
    if not_unifiable_fast 0 (target, f) then acc else sub :: acc
  in
  List.map List.rev @@ loop f [] []

(** Compute all the paths in a formula that lead to the left or right side of an equality
    which is in the first-order skeleton. *)
(*let eq_subs env context f : int list list =
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
  List.map List.rev @@ loop context f [] []*)

let match_name pattern lemma : bool =
  (* Check that the pattern is an exact substring of the lemma's name.
     The test is case-insensitive. *)
  let user_name = String.lowercase_ascii @@ Name.show lemma.l_user in
  let pattern = String.lowercase_ascii pattern in
  try
    ignore (String.find user_name pattern);
    true
  with Not_found -> false

let prepare_goal env proof lemma selection : Proof.t * Path.t * Path.t =
  let { g_id; g_pregoal = pregoal } = PathUtils.goal selection proof in
  (* Make a new (pre)goal that has :
     - the lemma as a local hypothesis.
     - its environment extended with the environment of the lemma database. *)
  let new_pregoal =
    let g_hyps =
      Hyps.add pregoal.g_hyps
        { h_name = lemma.l_full; h_form = lemma.l_form; h_gen = 0 }
    in
    let g_env = env in
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

(*let link_sfl selection proof lemma =
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
      (eq_subs goal.g_env Context.empty lemma.l_form)*)

let filter pattern_opt selection_opt proof =
  (* Get the list of lemmas. *)
  let old_db = Proof.get_db proof in
  let lemmas = Lemmas.to_list old_db in

  (* Filter the lemmas by name. *)
  let lemmas =
    match pattern_opt with
    | None -> lemmas
    | Some pattern -> List.filter (match_name pattern) lemmas
  in

  (* Filter the lemmas by selection. *)
  let lemmas =
    match selection_opt with
    | None -> lemmas
    | Some selection ->
        (* Compute the environment of the lemmas and of all the goals. *)
        let env =
          List.fold_left
            (fun env goal -> Env.union env goal.g_pregoal.g_env)
            (Lemmas.env old_db) (Proof.opened proof)
        in

        let sel_subterm = PathUtils.term selection proof in
        List.filter
          begin
            fun l ->
              (* Prepare the goal. *)
              let proof, lemma_path, selection =
                prepare_goal env proof l selection
              in
              (* Test against relevant links. As we are testing for subformula linking,
                 we only select subpaths of the lemma that lead to a formula. *)
              let subs = f_subs sel_subterm l.l_form in
              let hlpred = Link.Pred.wf_subform in
              List.exists
                begin
                  fun sub ->
                    not @@ List.is_empty
                    @@ hlpred proof ([ subpath lemma_path sub ], [ selection ])
                end
                subs
          end
          lemmas
  in

  (* Compute the new lemma database and proof. *)
  let new_db = Lemmas.of_list lemmas |> Lemmas.extend_env (Lemmas.env old_db) in
  Proof.set_db proof new_db
