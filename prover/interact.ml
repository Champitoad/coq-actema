(*open Utils.Pervasive
  open Api
  open Lang
  open Logic
  open ProverLogic

  (* For a backwards interaction, the first formula is the hypothesis,
     the second formula is the conclusion.
     For a forward interaction, the order doesn't matter. *)
  type state =
      { (* The itrace generated so far. The most recent choice is first. *)
        itrace : itrace
      ; (* The number of free variables in the first term . *)
        n_free_1 : int
      ; (* The number of free variables in the second term. *)
        n_free_2 : int
      ; (* The first focussed subterm. *)
        fo1 : FirstOrder.t
      ; (* The second focussed subterm. *)
        fo2 : FirstOrder.t
      ; (* The remaining subpath in [fo1]. *)
        sub1 : int list
      ; (* The remaining subpath in [fo2]. *)
        sub2 : int list
      ; (* The witnesses for the remaining instantiations in [fo1]. The next witness comes first.
           Each witness has open variables that live in the "common context"
           of the substitution (which was computed in [Link.ml]). *)
        witnesses1 : Term.t option list
      ; (* The witnesses for the remaining instantiations in [fo2]. The next witness comes first. *)
        witnesses2 : Term.t option list
      }

    type dnd_mode = Forward | Backward

    (** [instantiable state side] checks whether the next witness on [side]
        has all its free variables in scope (which means we are allowed to instantiate
        the corresponding quantifier).

        This assumes that the next witness on [side] is of the form [Some _]. *)
    let instantiable state (side : [ `Left | `Right ]) : bool =
      (* Get the witness. *)
      let witness =
        match side with
        | `Left -> Option.get @@ List.hd state.witnesses1
        | `Right -> Option.get @@ List.hd state.witnesses2
      in
      (* Compute the lowest variable that is in scope on each side. *)
      let in_scope_1 = List.length state.witnesses1 in
      let in_scope_2 = List.length state.witnesses2 in
      (* Check the free variables are in scope. *)
      let fvars_1, fvars_2 =
        IntSet.split_lt state.n_free_1 @@ TermUtils.free_vars witness
      in
      (* Performance is not an issue here. *)
      IntSet.for_all (fun v -> v >= in_scope_1) fvars_1
      && IntSet.for_all (fun v -> v - state.n_free_1 >= in_scope_2) fvars_2

    let take_if cond xs =
      match (cond, xs) with
      | false, _ -> (None, xs)
      | true, hd :: tl -> (hd, tl)
      | true, [] -> raise @@ Invalid_argument "take_if"

    let head_is_none xs : bool = match xs with None :: _ -> true | _ -> false
    let head_is_some xs : bool = match xs with Some _ :: _ -> true | _ -> false

    (* Step into the left formula. *)
    let left_step state ?(invert = false) ?(binder = false) fo1 sub1 =
      (* If [binder] is set, use the next witness from [witnesses1]. *)
      let the_witness, witnesses1 = take_if binder state.witnesses1 in
      (* If [invert] is set, change to Forward mode. *)
      let dnd_mode = if invert then Forward else Backward in
      (* Compute the new state. *)
      let state =
        { state with
          itrace = (0, the_witness) :: state.itrace
        ; fo1
        ; sub1
        ; witnesses1
        }
      in
      (state, dnd_mode)

    (* Step into the right formula. *)
    let right_step state ?(invert = false) ?(binder = false) fo2 sub2 =
      (* If [binder] is set, use the next witness from [witnesses2]. *)
      let the_witness, witnesses2 = take_if binder state.witnesses2 in
      (* If [invert] is set, change to Forward mode. *)
      let dnd_mode = if invert then Forward else Backward in
      (* Compute the new state. *)
      let state =
        { state with
          itrace = (1, the_witness) :: state.itrace
        ; fo2
        ; sub2
        ; witnesses2
        }
      in
      (state, dnd_mode)

    (** Perform a single backwards step.
        This returns the updated state and the next dnd mode. *)
    let backward_step (state : state) : state * dnd_mode =
      (* It is very important that we try the invertible rules before the other rules. *)
      match ((state.fo1, state.sub1), (state.fo2, state.sub2)) with
      (***********************************************************************)
      (* Right INVERTIBLE rules. *)
      (***********************************************************************)
      (* Rule R¬ *)
      | _, (FConn (Not, [ f0 ]), 0 :: sub) -> right_step state ~invert:true f0 sub
      (* Rule R⇒₁ *)
      | _, (FImpl (f0, f1), 0 :: sub) -> right_step state ~invert:true f0 sub
      (* Rule R⇒₂ *)
      | _, (FImpl (f0, f1), 1 :: sub) -> right_step state f1 sub
      (* Rule R⇔₁ *)
      | _, (FConn (Equiv, [ f1; f2 ]), 1 :: sub) -> failwith "backward_step: todo"
      (* Rule R⇔₂ *)
      | _, (FConn (Equiv, [ f1; f2 ]), 2 :: sub) -> failwith "backward_step: todo"
      (* Rule R∀s *)
      | _, (FBind (Forall, _, _, f1), 1 :: sub) when head_is_none state.witnesses2
        ->
          right_step state ~binder:true f1 sub
      (***********************************************************************)
      (* Left INVERTIBLE rules. *)
      (***********************************************************************)
      (* Rule L∨₁ *)
      | (FConn (Or, [ f1; f2 ]), 1 :: sub), _ -> left_step state f1 sub
      (* Rule L∨₂ *)
      | (FConn (Or, [ f1; f2 ]), 2 :: sub), _ -> left_step state f2 sub
      (* Rule L∃s *)
      | (FBind (Exist, _, _, f1), 2 :: 1 :: sub), _
        when head_is_none state.witnesses1 ->
          left_step state ~binder:true f1 sub
      (***********************************************************************)
      (* Right rules. *)
      (***********************************************************************)
      (* Rules R∧₁ and R∨₁ *)
      | _, (FConn (conn, [ f1; f2 ]), 1 :: sub) when conn = And || conn = Or ->
          right_step state f1 sub
      (* Rules R∧₂ and R∨₂ *)
      | _, (FConn (conn, [ f1; f2 ]), 2 :: sub) when conn = And || conn = Or ->
          right_step state f2 sub
      (* Rules R∃s and R∃i *)
      | _, (FBind (Exist, _, _, f1), 2 :: 1 :: sub)
        when head_is_none state.witnesses2
             || (head_is_some state.witnesses2 && instantiable state `Right) ->
          right_step state ~binder:true f1 sub
      (***********************************************************************)
      (* Left rules. *)
      (***********************************************************************)
      (* Rule L⇒₂ *)
      | (FImpl (f0, f1), 1 :: sub), _ -> left_step state f1 sub
      (* Rules L∧₁ and Rule L⇔₁ *)
      | (FConn (conn, [ f1; f2 ]), 1 :: sub), _ when conn = Or || conn = Equiv ->
          left_step state f1 sub
      (* Rules L∧₂ and L⇔₂ *)
      | (FConn (conn, [ f1; f2 ]), 2 :: sub), _ when conn = And || conn = Equiv ->
          left_step state f2 sub
      (* Rule L∀s and L∀i *)
      | (FBind (Forall, _, _, f1), 1 :: sub), _
        when head_is_none state.witnesses1
             || (head_is_some state.witnesses1 && instantiable state `Left) ->
          left_step state ~binder:true f1 sub
      (* No applicable rule. *)
      | _ -> failwith "Interact.backward_step : no rule is applicable."

    (** Perform a single forward step.
        This returns the updated state and the next dnd mode. *)
    let forward_step (state : state) : state * dnd_mode =
      (* It is very important that we try the invertible rules before the other rules. *)
      match ((state.fo1, state.sub1), (state.fo2, state.sub2)) with
      (***********************************************************************)
      (* INVERTIBLE rules. *)
      (***********************************************************************)
      (* Rule F∃s *)
      | _, (FBind (Exist, _, _, f1), 2 :: 1 :: sub)
        when head_is_none state.witnesses2 ->
          right_step state ~binder:true f1 sub
      | (FBind (Exist, _, _, f1), 2 :: 1 :: sub), _
        when head_is_none state.witnesses1 ->
          left_step state ~binder:true f1 sub
      (***********************************************************************)
      (* Non invertible rules. *)
      (***********************************************************************)
      (* Rules F∧₁ and F∨₁ *)
      | _, (FConn (conn, [ f1; f2 ]), 1 :: sub) when conn = And || conn = Or ->
          right_step state f1 sub
      | (FConn (conn, [ f1; f2 ]), 1 :: sub), _ when conn = And || conn = Or ->
          left_step state f1 sub
      (* Rules F∧₂ and F∨₂ *)
      | _, (FConn (conn, [ f1; f2 ]), 2 :: sub) when conn = And || conn = Or ->
          right_step state f2 sub
      | (FConn (conn, [ f1; f2 ]), 2 :: sub), _ when conn = And || conn = Or ->
          left_step state f2 sub
      (* Rule F⇒₁ *)
      | _, (FImpl (f0, f1), 0 :: sub) -> right_step state ~invert:true f0 sub
      | (FImpl (f0, f1), 0 :: sub), _ -> left_step state ~invert:true f0 sub
      (* Rule F⇒₂ *)
      | _, (FImpl (f0, f1), 1 :: sub) -> right_step state f1 sub
      | (FImpl (f0, f1), 1 :: sub), _ -> left_step state f1 sub
      (* Rule F¬ *)
      | _, (FConn (Not, [ f0 ]), 0 :: sub) -> right_step state ~invert:true f0 sub
      | (FConn (Not, [ f0 ]), 0 :: sub), _ -> left_step state ~invert:true f0 sub
      (* Rules F∀s and F∀i *)
      | _, (FBind (Forall, _, _, f1), 1 :: sub)
        when head_is_none state.witnesses2
             || (head_is_some state.witnesses2 && instantiable state `Right) ->
          right_step state ~binder:true f1 sub
      | (FBind (Forall, _, _, f1), 1 :: sub), _
        when head_is_none state.witnesses1
             || (head_is_some state.witnesses1 && instantiable state `Left) ->
          left_step state ~binder:true f1 sub
      (* No applicable rule. *)
      | _ -> failwith "Interact.forward_step : no rule is applicable."

    (** The main interaction loop. *)
    let rec interact ctx env (state : state) mode : itrace =
      Js_log.log
      @@ Format.sprintf "%s %s %s"
           (Notation.term_to_string ~ctx env @@ FirstOrder.to_term state.fo1)
           (match mode with Forward -> "*" | Backward -> "|-")
           (Notation.term_to_string ~ctx env @@ FirstOrder.to_term state.fo2);

      if state.sub1 = [] && state.sub2 = []
      then (* We finished the interaction. *)
        List.rev state.itrace
      else
        (* Perform one interaction step. *)
        match mode with
        | Forward -> forward_step state |> uncurry (interact ctx env)
        | Backward -> backward_step state |> uncurry (interact ctx env)

    let swap_sides state : state = failwith "swap_sides : todo"

    let dlink (src, dst) subst proof : itrace =
      (* Destruct the link. *)
      let env = (Proof.byid proof src.Path.goal).g_env in
      let src_term = term_of_item @@ PathUtils.item src proof in
      let dst_term = term_of_item @@ PathUtils.item dst proof in

      (* Massage the substitution into a format that we can use here. *)
      let witnesses =
        let open Unif in
        (* Note : we rely on the fact that IntMap.bindings returns the bindings
           by increasing key order. *)
        subst.mapping |> IntMap.bindings
        |> List.map (function
             | _, SRigid -> None
             | _, SFlex -> None
             | _, SBound term -> Some term)
      in
      let src_wits, dst_wits =
        pair_map List.rev @@ List.split_at subst.n_free_1 witnesses
      in

      Js_log.log
      @@ Format.sprintf "Source witnesses : %s"
           (List.to_string (Option.map_default Term.show "[none]") src_wits);
      Js_log.log
      @@ Format.sprintf "Dest witnesses : %s"
           (List.to_string (Option.map_default Term.show "[none]") dst_wits);

      (* Build the initial state. *)
      let state =
        { itrace = []
        ; n_free_1 = subst.n_free_1
        ; n_free_2 = subst.n_free_2
        ; fo1 = FirstOrder.of_term env src_term
        ; sub1 = src.sub
        ; witnesses1 = src_wits
        ; fo2 = FirstOrder.of_term env dst_term
        ; sub2 = dst.sub
        ; witnesses2 = dst_wits
        }
      in

      (* Compute the interaction. *)
      match (src.kind, dst.kind) with
      | Hyp _, Concl -> interact subst.context env state Backward
      | Concl, Hyp _ -> interact subst.context env (swap_sides state) Backward
      | Hyp _, Hyp _ -> interact subst.context env state Forward
      | _ -> failwith "Interact.dlink : invalid link."
*)

let dlink (src, dst) subst proof = failwith "dlink: todo"
