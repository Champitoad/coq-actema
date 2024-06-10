open Utils.Pervasive
open Api
open Lang
open Logic
open ProverLogic

(** [term_size term] computes the number of nodes in [term] (including leaves). *)
let rec term_size (term : Term.t) : int =
  match term with
  | BVar _ | FVar _ | Sort _ | Cst _ -> 1
  | App (_, f, args) -> List.sum @@ List.map term_size (f :: args)
  | Lambda (_, x, ty, body) | Prod (_, x, ty, body) ->
      term_size ty + term_size body

(** Get the raw subterm of a term, i.e. without instantiating BVars with FVars. *)
let rec subterm_raw (term : Term.t) sub : Term.t =
  match (sub, term) with
  | [], _ -> term
  | i :: sub, App (_, f, args) when 0 <= i && i < List.length (f :: args) ->
      subterm_raw (List.at (f :: args) i) sub
  | 0 :: sub, Lambda (_, x, ty, body) | 0 :: sub, Prod (_, x, ty, body) ->
      subterm_raw ty sub
  | 1 :: sub, Lambda (_, x, ty, body) | 1 :: sub, Prod (_, x, ty, body) ->
      subterm_raw body sub
  | _ -> failwith "Link.subterm_raw : invalid subpath"

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

(** A predicate type. *)
type hlpred_type = WfSubform | DeepRewrite

let eval_hlpred_type = function
  | WfSubform -> Link.Pred.wf_subform
  | DeepRewrite -> Link.Pred.deep_rewrite

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
          else (2 :: sub, DeepRewrite) :: acc
        in
        let acc =
          if not_unifiable 0 (target, arg3)
          then acc
          else (3 :: sub, DeepRewrite) :: acc
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
  if not_unifiable 0 (target, f) then acc else (sub, WfSubform) :: acc

(** Compute all the paths in a formula that lead to a subformula that :
    - is in the first order skeleton (including equality arguments).
    - is possibly unifiable with [target]. *)
let compute_subs target f : (int list * hlpred_type) list =
  compute_subs_rec target f [] []
  |> List.map (fun (sub, pred) -> (List.rev sub, pred))

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

(** This is the information that is gathered when a lemma matches a given selection. *)
type lemma_match =
  { (* The lemma that matches the selection. *)
    lemma : lemma
  ; (* The size of the lemma's formula. *)
    size : int
  ; (* The path to the subterm of the lemma that matches. *)
    sub : int list
  ; (* The size of the subterm of the lemma that matches. *)
    subterm_size : int
  ; (* The hyperlink predicate used for matching. *)
    pred : hlpred_type
  }

(** For efficiency reasons we move as much computation as possible out of this function. *)
let match_selection proof lemma env selection sel_subterm : lemma_match list =
  (* Prepare the goal. *)
  let proof, lemma_path, selection = prepare_goal env proof lemma selection in
  (* Test against relevant links. As we are testing for subformula linking,
     we only select subpaths of the lemma that lead to a formula. *)
  let subs = compute_subs sel_subterm lemma.l_form in
  List.filter_map
    begin
      fun (sub, pred) ->
        let hlpred = eval_hlpred_type pred in
        if not @@ List.is_empty
           @@ hlpred proof ([ subpath lemma_path sub ], [ selection ])
        then
          Some
            { lemma
            ; size = term_size lemma.l_form
            ; sub
            ; subterm_size = term_size @@ subterm_raw lemma.l_form sub
            ; pred
            }
        else None
    end
    subs

let best_match matches : lemma_match option =
  List.find_max (fun m -> term_size @@ subterm_raw m.lemma.l_form m.sub) matches

let match_name pattern lemma : bool =
  (* Check that the pattern is an exact substring of the lemma's name.
     The test is case-insensitive. *)
  let user_name = String.lowercase_ascii @@ Name.show lemma.l_user in
  let pattern = String.lowercase_ascii pattern in
  try
    ignore (String.find user_name pattern);
    true
  with Not_found -> false

(** Lexicographic ordering of names. *)
let name_compare n1 n2 : int =
  lex_compare Char.compare
    (String.explode @@ Name.show n1)
    (String.explode @@ Name.show n2)

(** Compare lemma matches. *)
let match_compare m1 m2 : int =
  (* We want a big subterm size but a small size. *)
  triple_compare (Fun.flip Int.compare) Int.compare name_compare
    (m1.subterm_size, m1.size, m1.lemma.l_user)
    (m2.subterm_size, m2.size, m2.lemma.l_user)

let nub_matches matches =
  let rec loop found acc = function
    | [] -> List.rev acc
    | m :: matches when Name.Set.mem m.lemma.l_full found ->
        loop found acc matches
    | m :: matches ->
        loop (Name.Set.add m.lemma.l_full found) (m :: acc) matches
  in
  loop Name.Set.empty [] matches

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

  (* Filter the lemmas by selection and sort them based on how well they match the selection. *)
  let lemmas =
    match selection_opt with
    | None ->
        (* If there is no selection, simply sort the lemmas by name. *)
        List.sort (fun l1 l2 -> name_compare l1.l_user l2.l_user) lemmas
    | Some selection ->
        (* Compute the environment of the lemmas and of all the goals. *)
        let env =
          List.fold_left
            (fun env goal -> Env.union env goal.g_pregoal.g_env)
            (Lemmas.env old_db) (Proof.opened proof)
        in

        let sel_subterm = PathUtils.term selection proof in
        let matches =
          lemmas
          |> (* Get the list of matches. *)
          List.concat_map (fun l ->
              match_selection proof l env selection sel_subterm)
          |> (* Sort the matches from best to worst. *)
          List.sort match_compare
          |> (* Keep only one match per lemma. *)
          nub_matches
        in
        Js_log.log @@ Format.sprintf "%d matches" (List.length matches);
        (* Get the (sorted) list of lemmas that match the selection. *)
        List.map (fun m -> m.lemma) matches
  in

  (* Reconstruct the lemma database. *)
  let new_db = Lemmas.of_list lemmas |> Lemmas.extend_env (Lemmas.env old_db) in
  Proof.set_db proof new_db
