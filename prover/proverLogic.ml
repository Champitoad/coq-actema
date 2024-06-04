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
          let check f = ignore (TermUtils.check g_pregoal.g_env f) in
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
      | Path.Hyp hname ->
          let hyp =
            try Hyps.by_name pregoal.g_hyps hname
            with InvalidHyphName _ -> raise exn
          in
          (Hyp (hname, hyp), hyp.h_form)
      | Path.VarHead vname ->
          let var =
            try Vars.by_name pregoal.g_vars vname
            with InvalidVarName _ -> raise exn
          in
          (Var (vname, var.v_type, var.v_body), Term.mkCst vname)
      | Path.VarType vname ->
          let var =
            try Vars.by_name pregoal.g_vars vname
            with InvalidVarName _ -> raise exn
          in
          (Var (vname, var.v_type, var.v_body), var.v_type)
      | Path.VarBody vname ->
          let var =
            try Vars.by_name pregoal.g_vars vname
            with InvalidVarName _ -> raise exn
          in
          let body = Option.get_exn var.v_body exn in
          (Var (vname, var.v_type, var.v_body), body)
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

  let rec of_subterm_rec env context pol term sub : t * Context.t * Term.t =
    let fo = FirstOrder.view env context term in
    match (sub, fo) with
    | [], _ -> (pol, context, term)
    (* Inverse the polarity. *)
    | 1 :: sub, FConn (Not, [ t1 ]) ->
        of_subterm_rec env context (opp pol) t1 sub
    | 0 :: sub, FImpl (t1, t2) -> of_subterm_rec env context (opp pol) t1 sub
    (* Switch to [Sup] polarity. *)
    | 1 :: sub, FConn (Equiv, [ t1; t2 ]) ->
        of_subterm_rec env context Sup t1 sub
    | 2 :: sub, FConn (Equiv, [ t1; t2 ]) ->
        of_subterm_rec env context Sup t2 sub
    (* Recurse in the formula. *)
    | 1 :: sub, FImpl (t1, t2) -> of_subterm_rec env context pol t2 sub
    | i :: sub, FConn (conn, ts) when 1 <= i && i <= List.length ts ->
        of_subterm_rec env context pol (List.at ts (i - 1)) sub
    (* Binders. *)
    | 1 :: sub, FBind (Forall, x, ty, body) ->
        let fvar, context = Context.add_fresh x ty context in
        let body = Term.instantiate fvar body in
        of_subterm_rec env context pol body sub
    | 2 :: 1 :: sub, FBind (Exist, x, ty, body) ->
        let fvar, context = Context.add_fresh x ty context in
        let body = Term.instantiate fvar body in
        of_subterm_rec env context pol body sub
    (* The path is either invalid or escapes the first-order skeleton. *)
    | _ -> raise @@ InvalidSubtermPath (term, sub)

  let of_subterm env pol term sub : t * Context.t * Term.t =
    of_subterm_rec env Context.empty pol term sub

  (** This assumes that [t] has type [Prop]. *)
  let rec neg_count_rec env context negs (term : Term.t) sub :
      int * Context.t * Term.t =
    let fo = FirstOrder.view env context term in
    match (sub, fo) with
    | [], _ -> (negs, context, term)
    (* Increase the negation count. *)
    | 1 :: sub, FConn (Not, [ t1 ]) ->
        neg_count_rec env context (negs + 1) t1 sub
    | 0 :: sub, FImpl (t1, t2) -> neg_count_rec env context (negs + 1) t1 sub
    (* Recurse in the formula. *)
    | 1 :: sub, FImpl (t1, t2) -> neg_count_rec env context negs t2 sub
    | i :: sub, FConn (conn, ts) when 1 <= i && i <= List.length ts ->
        neg_count_rec env context negs (List.at ts (i - 1)) sub
    (* Binders. *)
    | 1 :: sub, FBind (Forall, x, ty, body) ->
        let fvar, context = Context.add_fresh x ty context in
        let body = Term.instantiate fvar body in
        neg_count_rec env context negs body sub
    | 2 :: 1 :: sub, FBind (Exist, x, ty, body) ->
        let fvar, context = Context.add_fresh x ty context in
        let body = Term.instantiate fvar body in
        neg_count_rec env context negs body sub
    (* The path is either invalid or escapes the first-order skeleton. *)
    | _ -> raise @@ InvalidSubtermPath (term, sub)

  let neg_count env term sub : int =
    let negs, _, _ = neg_count_rec env Context.empty 0 term sub in
    negs

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
