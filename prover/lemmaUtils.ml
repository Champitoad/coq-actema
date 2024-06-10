open Utils.Pervasive
open Api
open Lang
open Logic
open ProverLogic

(** Function to test whether two terms [t1] and [t2] are *not* unifiable.
    - If it returns [true] then [t1] and [t2] are *not* unifiable. 
    - If it returns [false] we didn't gain any information. 
    This assumes syntactic unification.

    For efficiency reasons this function operates directly on de Bruijn syntax 
    instead of locally nameless syntax. *)
let rec not_unifiable depth ((t1, t2) : Term.t * Term.t) : bool =
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
      List.exists (not_unifiable depth)
      @@ List.combine (f1 :: args1) (f2 :: args2)
  | Lambda (_, x1, ty1, body1), Lambda (_, x2, ty2, body2)
  | Prod (_, x1, ty1, body1), Prod (_, x2, ty2, body2) ->
      not_unifiable depth (ty1, ty2) || not_unifiable (depth + 1) (body1, body2)
  (* In every other case [t1] and [t2] are *not* unifiable. *)
  | _ -> true

let rec compute_subs_rec target f sub acc =
  (* Deal with subformulas. *)
  let acc =
    match FirstOrder.view Env.empty Context.empty f with
    (* Equality : we might be able to perform a deep rewrite. *)
    | FAtom (App (_, Cst eq, [ _; arg2; arg3 ])) when Name.equal eq Constants.eq
      ->
        let acc =
          if not_unifiable 0 (target, arg2)
          then acc
          else (2 :: sub, Link.Pred.deep_rewrite) :: acc
        in
        let acc =
          if not_unifiable 0 (target, arg3)
          then acc
          else (3 :: sub, Link.Pred.deep_rewrite) :: acc
        in
        acc
    | FAtom _ -> acc
    | FConn (conn, args) ->
        List.fold_lefti
          (fun acc i arg -> compute_subs_rec target arg ((i + 1) :: sub) acc)
          acc args
    | FImpl (f0, f1) ->
        let acc = compute_subs_rec target f0 (0 :: sub) acc in
        compute_subs_rec target f1 (1 :: sub) acc
    (* For Forall/Exist we don't recurse in the type of the binder. *)
    | FBind (Forall, x, ty, body) -> compute_subs_rec target body (1 :: sub) acc
    | FBind (Exist, x, ty, body) ->
        compute_subs_rec target body (1 :: 2 :: sub) acc
  in
  (* We might be able to perform subformula linking. *)
  if not_unifiable 0 (target, f)
  then acc
  else (sub, Link.Pred.wf_subform) :: acc

(** Compute all the paths in a formula that lead to a subformula that :
    - is in the first order skeleton (including equality arguments).
    - is possibly unifiable with [target]. *)
let compute_subs target f : (int list * Link.Pred.hlpred) list =
  compute_subs_rec target f [] []
  |> List.map (fun (sub, pred) -> (List.rev sub, pred))

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

(** For efficiency reasons we move as much computation as possible out of this function. *)
let linkable proof lemma env selection sel_subterm =
  (* Prepare the goal. *)
  let proof, lemma_path, selection = prepare_goal env proof lemma selection in
  (* Test against relevant links. As we are testing for subformula linking,
     we only select subpaths of the lemma that lead to a formula. *)
  let subs = compute_subs sel_subterm lemma.l_form in
  List.exists
    begin
      fun (sub, pred) ->
        not @@ List.is_empty
        @@ pred proof ([ subpath lemma_path sub ], [ selection ])
    end
    subs

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

        (* Test if each lemma is linkable with the selected subterm. *)
        let sel_subterm = PathUtils.term selection proof in
        List.filter (fun l -> linkable proof l env selection sel_subterm) lemmas
  in

  (* Compute the new lemma database and proof. *)
  let new_db = Lemmas.of_list lemmas |> Lemmas.extend_env (Lemmas.env old_db) in
  Proof.set_db proof new_db
