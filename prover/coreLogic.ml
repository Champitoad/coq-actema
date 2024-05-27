open Utils.Pervasive
open Api
open Lang
open Logic

exception SubgoalNotOpened of int

module IntNameMap = Map.Make (struct
  type t = int * Name.t

  let compare = Stdlib.compare
end)

module Proof = struct
  type mkey =
    | MProof
    | MGoal of int
    | MHyp of int * Name.t
    | MVar of int * Name.t

  module MKeyMap = Map.Make (struct
    type t = mkey

    let compare = compare
  end)

  type mdata = < > Js_of_ocaml.Js.t

  type t =
    { p_goals : goal IntMap.t
          (** A map from goal handles to goals. 
              Contains only the opened (i.e. currently active) goals. *)
    ; p_meta : mdata MKeyMap.t ref  (** Metadata. *)
    ; p_db : Lemmas.t  (** The lemma database. *)
    }

  let init goals =
    (* Type-check the goals, just to make sure. *)
    List.iter
      begin
        fun { g_id; g_pregoal } ->
          let check f = ignore (Typing.check g_pregoal.g_env f) in
          check g_pregoal.g_concl;
          Hyps.iter
            (fun { h_name; h_gen; h_form } -> check h_form)
            g_pregoal.g_hyps
      end
      goals;
    (* Create the map from goal handles to goals. *)
    let p_goals =
      List.fold_left
        (fun p_goals g ->
          assert (not @@ IntMap.mem g.g_id p_goals);
          IntMap.add g.g_id g p_goals)
        IntMap.empty goals
    in
    { p_goals; p_meta = ref MKeyMap.empty; p_db = Lemmas.empty }

  let get_db (proof : t) = proof.p_db
  let set_db (proof : t) (db : Lemmas.t) = { proof with p_db = db }

  let set_meta proof key meta : unit =
    match meta with
    | None -> proof.p_meta := MKeyMap.remove key !(proof.p_meta)
    | Some meta -> proof.p_meta := MKeyMap.add key meta !(proof.p_meta)

  let get_meta proof key : mdata option = MKeyMap.find_opt key !(proof.p_meta)
  let is_closed (proof : t) = IntMap.is_empty proof.p_goals
  let opened (proof : t) = IntMap.keys proof.p_goals |> List.of_enum

  let byid (proof : t) (goal_id : int) : pregoal =
    let goal =
      Option.get_exn
        (IntMap.find_opt goal_id proof.p_goals)
        (InvalidGoalId goal_id)
    in
    goal.g_pregoal

  exception TacticNotApplicable

  let xprogress (proof : t) (goal_id : int) (pregoals : pregoal list) =
    (* Get the maximum goal index currently in use. *)
    let max_id = proof.p_goals |> IntMap.keys |> List.of_enum |> List.max in
    (* Choose a goal id for each pregoal. *)
    let subgoals =
      let for1 i subgoal =
        let hyps = Hyps.bump subgoal.g_hyps in
        let sub = { subgoal with g_hyps = hyps } in
        { g_id = max_id + i + 1; g_pregoal = sub }
      in
      List.mapi for1 pregoals
    in
    let new_ids = List.map (fun x -> x.g_id) subgoals in

    (* The new subgoals get the same metadata as the old goal. *)
    let p_meta =
      match get_meta proof (MGoal goal_id) with
      | None -> !(proof.p_meta)
      | Some meta ->
          List.fold_left
            (fun map id -> MKeyMap.add (MGoal id) meta map)
            !(proof.p_meta) new_ids
    in

    (* Remove the old goal and add the new goals. *)
    let p_goals =
      proof.p_goals |> IntMap.remove goal_id
      |> List.fold_right
           (fun subgoal map -> IntMap.add subgoal.g_id subgoal map)
           subgoals
    in
    (* Don't forget to return the indices of the new goals. *)
    (new_ids, { proof with p_goals; p_meta = ref p_meta })

  let ivariants proof ~goal_id =
    match (byid proof goal_id).g_concl with
    | App (Cst name, _) ->
        if name = Name.eq
        then [ "reflexivity" ]
        else if name = Name.and_
        then [ "split" ]
        else if name = Name.or_
        then [ "left"; "right" ]
        else if name = Name.equiv
        then [ "split" ]
        else if name = Name.not
        then [ "intro" ]
        else if name = Name.ex
        then [ "exists" ]
        else []
    | Cst name when name = Name.true_ -> [ "constructor" ]
    | Arrow _ | Prod _ | Lambda _ -> [ "intro" ]
    | _ -> []

  let evariants proof ~goal_id ~hyp_name =
    match (Hyps.by_name (byid proof goal_id).g_hyps hyp_name).h_form with
    | App (Cst name, _) ->
        if name = Name.eq
        then [ "rewrite->"; "rewrite<-" ]
        else if name = Name.equiv
        then [ "destruct" ]
        else if name = Name.or_
        then [ "destruct" ]
        else if name = Name.not
        then [ "destruct " ]
        else if name = Name.ex
        then [ "destruct" ]
        else []
    | Cst name ->
        if name = Name.true_
        then [ "destruct" ]
        else if name = Name.false_
        then [ "destruct" ]
        else []
    | Arrow _ -> [ "apply" ]
    | _ -> []

  let move proof ~goal_id ~hyp_name ~dest_name =
    let goal = byid proof goal_id in
    let hyps = Hyps.move goal.g_hyps hyp_name dest_name in

    snd @@ xprogress proof goal_id [ { goal with g_hyps = hyps } ]
end

module PathUtils = struct
  let destr path proof : goal * item * Context.t * Term.t =
    let exn = Path.InvalidPath (Path.to_string path) in
    let pregoal =
      try Proof.byid proof path.goal with InvalidGoalId _ -> raise exn
    in

    let item, i_term =
      match path.kind with
      | Path.Concl -> (Concl pregoal.g_concl, pregoal.g_concl)
      | Path.Hyp hid ->
          let hyp =
            try Hyps.by_name pregoal.g_hyps hid
            with InvalidHyphName _ -> raise exn
          in
          (Hyp (hid, hyp), hyp.h_form)
      | _ -> failwith "PathUtils.dest : todo"
    in
    let ctx, term =
      try TermUtils.subterm i_term path.sub
      with InvalidSubtermPath _ -> raise exn
    in
    ({ g_id = path.goal; g_pregoal = pregoal }, item, ctx, term)

  let goal path proof : goal =
    let g, _, _, _ = destr path proof in
    g

  let gid path proof : int = (goal path proof).g_id

  let item path proof : item =
    let _, item, _, _ = destr path proof in
    item

  let term path proof : Term.t =
    let _, _, _, t = destr path proof in
    t

  let ctx path proof : Context.t =
    let _, _, ctx, _ = destr path proof in
    ctx

  let to_concl { g_id; _ } = Path.make g_id
end

(* -------------------------------------------------------------------- *)
(** Polarities *)

module Polarity = struct
  type t = Pos | Neg | Sup [@@deriving show]

  let opp = function Pos -> Neg | Neg -> Pos | Sup -> Sup

  let rec of_subterm_rec pol context (fo : FirstOrder.t) sub :
      t * (Context.t * Term.t) =
    match (sub, fo) with
    | [], _ -> (pol, (context, FirstOrder.to_term fo))
    (* Inverse the polarity. *)
    | 1 :: sub, FConn (Not, [ t1 ]) -> of_subterm_rec (opp pol) context t1 sub
    | 0 :: sub, FImpl (t1, t2) -> of_subterm_rec (opp pol) context t1 sub
    (* Switch to [Sup] polarity. *)
    | 1 :: sub, FConn (Equiv, [ t1; t2 ]) -> of_subterm_rec Sup context t1 sub
    | 2 :: sub, FConn (Equiv, [ t1; t2 ]) -> of_subterm_rec Sup context t2 sub
    (* Recurse in the formula. *)
    | 1 :: sub, FImpl (t1, t2) -> of_subterm_rec pol context t2 sub
    | i :: sub, FConn (conn, ts) when 1 <= i && i <= List.length ts ->
        of_subterm_rec pol context (List.at ts (i - 1)) sub
    (* Binders. *)
    | 1 :: sub, FBind (Forall, x, ty, body) ->
        of_subterm_rec pol (Context.push x ty context) body sub
    | 2 :: 1 :: sub, FBind (Exist, x, ty, body) ->
        of_subterm_rec pol (Context.push x ty context) body sub
    (* The path is either invalid or escapes the first-order skeleton. *)
    | _ -> raise @@ InvalidSubtermPath (FirstOrder.to_term fo, sub)

  let of_subterm env pol term sub : t * Context.t * Term.t =
    let fo = FirstOrder.of_term env term in
    let pol, (ctx, t) = of_subterm_rec pol Context.empty fo sub in
    (pol, ctx, t)

  (** This assumes that [t] has type [Prop]. *)
  (*let rec neg_count_rec exn (negs : int) context t sub :
      int * (Context.t * Term.t) =
    match sub with
    | [] -> (negs, (context, t))
    | idx :: sub -> begin
        match (t : Term.t) with
        (* Invalid terms at this point. *)
        | Var _ | Cst _ | Sort _ -> raise exn
        (* Traverse a [not]. *)
        | App (Cst f, [ arg ]) when Name.equal f Name.not && idx = 1 ->
            neg_count_rec exn (negs + 1) context arg sub
        (* Implication. *)
        | Arrow (t1, t2) -> begin
            match idx with
            | 0 -> neg_count_rec exn (negs + 1) context t1 sub
            | 1 -> neg_count_rec exn negs context t2 sub
            | _ -> raise exn
          end
        (* Any other logical connector. *)
        | App (Cst c, args) when Name.is_logical_conn c -> begin
            match idx with
            | 0 when sub = [] -> (negs, (context, Term.mkCst c))
            | i when 1 <= i && i <= List.length args ->
                neg_count_rec exn negs context (List.at args (i - 1)) sub
            | _ -> raise exn
          end
        (* Anpther application (not a logical connector) : stop counting negations. *)
        | App _ -> (negs, TermUtils.subterm ~context t (idx :: sub))
        (* Products. *)
        | Prod (x, ty, body) -> begin
            match idx with
            | 0 -> (negs, TermUtils.subterm ~context ty sub)
            | 1 -> neg_count_rec exn negs (Context.push x ty context) body sub
            | _ -> raise exn
          end
        (* Lambdas are not of type Prop. *)
        | Lambda _ -> raise exn
      end*)

  (*let neg_count term sub : int = failwith "neg_count: todo"
    let exn = InvalidSubtermPath (term, sub) in
      let negs, _ = neg_count_rec exn 0 Context.empty term sub in
      negs*)

  let of_item item : t = match item with Concl _ -> Pos | Var _ | Hyp _ -> Neg

  let of_ipath proof path : t =
    let goal, item, _, _ = PathUtils.destr path proof in
    let pol, form =
      match item with
      | Hyp (_, { h_form = f; _ }) -> (Neg, f)
      | Concl f -> (Pos, f)
      | Var _ ->
          raise
          @@ Invalid_argument "Polarity.of_ipath : path points to a variable."
    in
    let pol, _, _ = of_subterm goal.g_pregoal.g_env pol form path.sub in
    pol
end
