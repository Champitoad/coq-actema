open Utils
open Api
open Lang
open Logic
open Js_of_ocaml

exception InvalidSubFormPath of int list
exception InvalidSubExprPath of int list
exception SubgoalNotOpened of int

module IntNameMap = Map.Make (struct
  type t = int * Name.t

  let compare = Stdlib.compare
end)

module Proof = struct
  type meta = < > Js.t

  type t =
    { p_goals : goal IntMap.t
          (** A map from goal handles to goals. 
              Contains only the opened (i.e. currently active) goals. *)
    ; p_meta : meta option ref  (** Metadata associated to the proof. *)
    ; p_goal_meta : meta IntMap.t ref  (** Metadata associated to each goal. *)
    ; p_hyp_meta : meta IntNameMap.t ref
          (** Metadata associated to each hypothesis. *)
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
    { p_goals
    ; p_meta = ref None
    ; p_goal_meta = ref IntMap.empty
    ; p_hyp_meta = ref IntNameMap.empty
    ; p_db = Lemmas.empty
    }

  let get_db (proof : t) = proof.p_db
  let set_db (proof : t) (db : Lemmas.t) = { proof with p_db = db }
  let set_proof_meta proof meta : unit = proof.p_meta := meta
  let get_proof_meta proof : meta option = !(proof.p_meta)

  let set_goal_meta proof ~goal_id meta : unit =
    match meta with
    | None -> proof.p_goal_meta := IntMap.remove goal_id !(proof.p_goal_meta)
    | Some meta ->
        proof.p_goal_meta := IntMap.add goal_id meta !(proof.p_goal_meta)

  let get_goal_meta proof ~goal_id : meta option =
    IntMap.find_opt goal_id !(proof.p_goal_meta)

  let set_hyp_meta proof ~goal_id ~hyp_name meta : unit =
    match meta with
    | None ->
        proof.p_hyp_meta :=
          IntNameMap.remove (goal_id, hyp_name) !(proof.p_hyp_meta)
    | Some meta ->
        proof.p_hyp_meta :=
          IntNameMap.add (goal_id, hyp_name) meta !(proof.p_hyp_meta)

  let get_hyp_meta proof ~goal_id ~hyp_name : meta option =
    IntNameMap.find_opt (goal_id, hyp_name) !(proof.p_hyp_meta)

  let closed (proof : t) = IntMap.is_empty proof.p_goals
  let opened (proof : t) = IntMap.keys proof.p_goals |> List.of_enum

  let byid (proof : t) (goal_id : int) : pregoal =
    let goal =
      Option.get_exn
        (IntMap.Exceptionless.find goal_id proof.p_goals)
        (InvalidGoalId goal_id)
    in
    goal.g_pregoal

  exception TacticNotApplicable

  let xprogress (pr : t) (id : int) (subs : pregoal list) =
    failwith "Proof.xprogress : todo"
  (*(* Promote the pregoals to actual goals. *)
    let subs =
      let for1 sub =
        let hyps = Hyps.bump sub.g_hyps in
        let sub = { sub with g_hyps = hyps } in
        { g_id = Handle.fresh (); g_pregoal = sub }
      in
      List.map for1 subs
    in

    (* The handles of the new goals. *)
    let g_new = List.map (fun x -> x.g_id) subs in

    (* The new goals get the same metadata as the old goal. *)
    let meta =
      match Map.Exceptionless.find id !(pr.p_meta) with
      | None -> !(pr.p_meta)
      | Some meta ->
          List.fold_left (fun map id -> Map.add id meta map) !(pr.p_meta) g_new
    in

    (* Remove the old goal and add the new goals. *)
    let p_goals =
      pr.p_goals |> Map.remove id
      |> List.fold_right (fun sub map -> Map.add sub.g_id sub map) subs
    in
    (* Don't forget to return the handles of the new goals. *)
    (g_new, { pr with p_goals; p_meta = ref meta })*)

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
        then [ "into" ]
        else if name = Name.ex
        then [ "exists" ]
        else []
    | Cst name when name = Name.true_ -> [ "constructor" ]
    | Arrow _ | Prod _ | Lambda _ -> [ "intro" ]
    | _ -> []

  let evariants proof ~goal_id ~hyp_name =
    match (Hyps.byid (byid proof goal_id).g_hyps hyp_name).h_form with
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
            try Hyps.byid pregoal.g_hyps hid
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

  let rec of_subterm_rec exn pol ctx t sub : t * Context.t * Term.t =
    match sub with
    | [] -> (pol, ctx, t)
    | idx :: sub -> begin
        match (t : Term.t) with
        | Var _ | Cst _ | Sort _ -> raise exn
        | App (f, args) ->
            if idx = 0
            then of_subterm_rec exn pol ctx f sub
            else if 1 <= idx && idx <= List.length args
            then of_subterm_rec exn pol ctx (List.nth args (idx - 1)) sub
            else raise exn
        | Lambda (x, ty, body) | Prod (x, ty, body) ->
            if idx = 0
            then of_subterm_rec exn (opp pol) ctx ty sub
            else if idx = 1
            then of_subterm_rec exn pol (Context.push x ty ctx) body sub
            else raise exn
        | Arrow (t1, t2) ->
            if idx = 0
            then of_subterm_rec exn (opp pol) ctx t1 sub
            else if idx = 1
            then of_subterm_rec exn pol ctx t2 sub
            else raise exn
      end

  let of_subterm (pol, term) sub : t * Context.t * Term.t =
    let exn = InvalidSubtermPath (term, sub) in
    of_subterm_rec exn pol Context.empty term sub

  let neg_count term sub : int = failwith "neg_count: todo"
  let of_item item : t = match item with Concl _ -> Pos | Var _ | Hyp _ -> Neg

  let of_ipath proof path : t =
    let pol, form =
      match PathUtils.item path proof with
      | Hyp (_, { h_form = f; _ }) -> (Neg, f)
      | Concl f -> (Pos, f)
      | Var _ -> failwith "Polarity.of_ipath : path points to a variable."
    in
    let pol, _, _ = of_subterm (pol, form) path.sub in
    pol
end
