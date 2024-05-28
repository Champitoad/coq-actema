open Utils.Pervasive
open Api
open Lang
open Logic
open ProverLogic

(* For a backwards interaction, the first formula is the hypothesis,
   the second formula is the conclusion.
   For a forward interaction, the order doesn't matter. *)
type state =
  { n_free_1 : int
  ; n_free_2 : int
        (* The itrace generated so far. The most recent choice is first. *)
  ; itrace : itrace
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

(*let invertible (kind : [ `Left | `Right | `Forward ]) (f : FirstOrder.t) : bool
      =
    match kind with
    (* Right invertible *)
    | `Right -> begin
        match f with
        | FConn (Not, _) | FConn (Equiv, _) | FImpl _ | FBind (Forall, _, _, _) ->
            true
        | _ -> false
      end
    (* Left invertible *)
    | `Left -> begin
        match f with FConn (Or, _) | FBind (Exist, _, _, _) -> true | _ -> false
      end
    (* Forward invertible *)
    | `Forward -> begin
        match f with FBind (Exist, _, _, _) -> true | _ -> false
      end

  let no_prio (kind : [ `Left | `Right | `Forward ])
      ((f, sub) : FirstOrder.t * int list) =
    (not (invertible kind f)) || List.is_empty sub*)

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

(** Perform a single backwards step. 
    This returns the updated state, and the next dnd mode. *)
let backward_step (state : state) : state * dnd_mode =
  (* Step into the right formula (the conclusion). *)
  let right_step ?(invert = false) ?(binder = false) fo2 sub2 =
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
  in
  (* Step into the left formula (the hypothesis). *)
  let left_step ?(invert = false) ?(binder = false) fo1 sub1 =
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
  in
  (* It is very important that we try the invertible rules before the other rules. *)
  match ((state.fo1, state.sub1), (state.fo2, state.sub2)) with
  (***********************************************************************)
  (* Right INVERTIBLE rules. *)
  (***********************************************************************)
  (* Rule R¬ *)
  | _, (FConn (Not, [ f0 ]), 0 :: sub) -> right_step ~invert:true f0 sub
  (* Rule R⇒₁ *)
  | _, (FImpl (f0, f1), 0 :: sub) -> right_step ~invert:true f0 sub
  (* Rule R⇒₂ *)
  | _, (FImpl (f0, f1), 1 :: sub) -> right_step f1 sub
  (* Rule R⇔₁ *)
  | _, (FConn (Equiv, [ f1; f2 ]), 1 :: sub) -> right_step f1 sub
  (* Rule R⇔₂ *)
  | _, (FConn (Equiv, [ f1; f2 ]), 2 :: sub) -> right_step f2 sub
  (* Rule R∀s *)
  | _, (FBind (Forall, _, _, f1), 1 :: sub) when head_is_none state.witnesses2
    ->
      right_step ~binder:true f1 sub
  (***********************************************************************)
  (* Left INVERTIBLE rules. *)
  (***********************************************************************)
  (* Rule L∨₁ *)
  | (FConn (Or, [ f1; f2 ]), 1 :: sub), _ -> left_step f1 sub
  (* Rule L∨₂ *)
  | (FConn (Or, [ f1; f2 ]), 2 :: sub), _ -> left_step f2 sub
  (* Rule L∃s *)
  | (FBind (Exist, _, _, f1), 2 :: 1 :: sub), _
    when head_is_none state.witnesses1 ->
      left_step ~binder:true f1 sub
  (***********************************************************************)
  (* Right rules. *)
  (***********************************************************************)
  (* Rule R∧₁ *)
  | _, (FConn (And, [ f1; f2 ]), 1 :: sub) -> right_step f1 sub
  (* Rule R∧₂ *)
  | _, (FConn (And, [ f1; f2 ]), 2 :: sub) -> right_step f2 sub
  (* Rule R∨₁ *)
  | _, (FConn (Or, [ f1; f2 ]), 1 :: sub) -> right_step f1 sub
  (* Rule R∨₂ *)
  | _, (FConn (Or, [ f1; f2 ]), 2 :: sub) -> right_step f2 sub
  (* Rule R∃s *)
  | _, (FBind (Exist, _, _, f1), 2 :: 1 :: sub)
    when head_is_none state.witnesses2 ->
      right_step ~binder:true f1 sub
  (* Rule R∃i *)
  | _, (FBind (Exist, _, _, f1), 2 :: 1 :: sub)
    when head_is_some state.witnesses2 && instantiable state `Right ->
      right_step ~binder:true f1 sub
  (* Rule R∃i *)
  | _, (FBind (Exist, _, _, f1), 2 :: 1 :: sub)
    when head_is_some state.witnesses2 ->
      right_step ~binder:true f1 sub
  (***********************************************************************)
  (* Left rules. *)
  (***********************************************************************)
  (* Rule L⇒₂ *)
  | (FImpl (f0, f1), 1 :: sub), _ -> left_step f1 sub
  (* Rule L∧₁ *)
  | (FConn (And, [ f1; f2 ]), 1 :: sub), _ -> left_step f1 sub
  (* Rule L∧₂ *)
  | (FConn (And, [ f1; f2 ]), 2 :: sub), _ -> left_step f2 sub
  (* Rule L⇔₁ *)
  | (FConn (Equiv, [ f1; f2 ]), 1 :: sub), _ -> left_step f1 sub
  (* Rule L⇔₂ *)
  | (FConn (Equiv, [ f1; f2 ]), 2 :: sub), _ -> left_step f2 sub
  (* Rule L∀s *)
  | (FBind (Forall, _, _, f1), 1 :: sub), _ when head_is_none state.witnesses1
    ->
      left_step ~binder:true f1 sub
  (* Rule L∀i *)
  | (FBind (Forall, _, _, f1), 1 :: sub), _
    when head_is_some state.witnesses1 && instantiable state `Left ->
      left_step ~binder:true f1 sub
  | _ -> failwith "Interact.backward_step : no rule is applicable."

(** Backward-mode interaction. *)
let rec backward (state : state) : itrace =
  (*Js_log.log @@ show_linkage goal.g_env `Backward linkage;*)
  if state.sub1 = [] && state.sub2 = []
  then (* We finished the interaction. *)
    List.rev state.itrace
  else
    (* Perform one interaction step. *)
    let state, next_mode = backward_step state in
    (* Recurse in forward or backward mode. *)
    match next_mode with Backward -> backward state | Forward -> forward state

(** Forward-mode interaction. *)
and forward (state : state) : itrace = failwith "foward : todo"

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

  (* Build the initial state and compute the interaction. *)
  match (src.kind, dst.kind) with
  | Hyp _, Concl ->
      backward
        { n_free_1 = subst.n_free_1
        ; n_free_2 = subst.n_free_2
        ; itrace = []
        ; fo1 = FirstOrder.of_term env src_term
        ; sub1 = src.sub
        ; witnesses1 = src_wits
        ; fo2 = FirstOrder.of_term env dst_term
        ; sub2 = dst.sub
        ; witnesses2 = dst_wits
        }
  | Concl, Hyp _ ->
      backward
        { n_free_1 = subst.n_free_1
        ; n_free_2 = subst.n_free_2
        ; itrace = []
        ; fo1 = FirstOrder.of_term env dst_term
        ; sub1 = dst.sub
        ; witnesses1 = dst_wits
        ; fo2 = FirstOrder.of_term env src_term
        ; sub2 = src.sub
        ; witnesses2 = src_wits
        }
  | Hyp _, Hyp _ ->
      forward
        { n_free_1 = subst.n_free_1
        ; n_free_2 = subst.n_free_2
        ; itrace = []
        ; fo1 = FirstOrder.of_term env src_term
        ; sub1 = src.sub
        ; witnesses1 = src_wits
        ; fo2 = FirstOrder.of_term env dst_term
        ; sub2 = dst.sub
        ; witnesses2 = dst_wits
        }
  | _ -> failwith "Interact.dlink : invalid link."

(*match
    (src_item, src_path.sub, src_wits, dst_item, dst_path.sub, dst_wits)
  with
  (* Start in backward mode. *)
  | ( Hyp (_, { h_form = hyp_term; _ })
    , hyp_sub
    , hyp_wits
    , Concl concl_term
    , concl_sub
    , concl_wits )
  | ( Concl concl_term
    , concl_sub
    , concl_wits
    , Hyp (_, { h_form = hyp_term; _ })
    , hyp_sub
    , hyp_wits ) ->
      backward
        { itrace = []
        ; fo1 = FirstOrder.of_term env hyp_term
        ; sub1 = hyp_sub
        ; witnesses1 = hyp_wits
        ; fo2 = FirstOrder.of_term env concl_term
        ; sub2 = concl_sub
        ; witnesses2 = concl_wits
        }
  (* Start in forward mode. *)
  | ( Hyp (_, { h_form = term1; _ })
    , sub1
    , wits1
    , Hyp (_, { h_form = term2; _ })
    , sub2
    , wits2 ) ->
      forward
        { itrace = []
        ; fo1 = FirstOrder.of_term env term1
        ; sub1
        ; witnesses1 = wits1
        ; fo2 = FirstOrder.of_term env term2
        ; sub2
        ; witnesses2 = wits2
        }
  | _ -> failwith "Interact.dlink : invalid link."*)

(*match ((item_src, sub_src, s_src), (item_dst, sub_dst, s_dst)) with
    | (`H (hid, { h_form = h; _ }), subh, sh), (`C c, subc, sc)
    | (`C c, subc, sc), (`H (hid, { h_form = h; _ }), subh, sh) ->
        let form, itrace =
          backward [] []
            ((LEnv.empty, sh), (LEnv.empty, sc))
            ((h, subh), (c, subc))
        in
        (([ (Some hid, []) ], form |> elim_units), itrace)
    | ( (`H (hid, { h_form = h; _ }), subh, s)
      , (`H (hid', { h_form = h'; _ }), subh', s') ) ->
        let form, itrace =
          forward [] []
            ((LEnv.empty, s), (LEnv.empty, s'))
            ((h, subh), (h', subh'))
        in
        ( ([ (Some hid, []); (Some hid', [ form |> elim_units ]) ], goal.g_goal)
        , itrace )
    | _ -> raise Tactics.TacticNotApplicable
  in
  List.rev itrace*)

(* backward_core ctx s switch_pol linkage
   in
   let cont = if !switch_pol then forward ~side:1 else backward in
   let ctx = match ictx with Some i -> i :: ctx | None -> ctx in
   cont ctx (choice :: itrace) !s linkage*)

(* (** [elim_units f] eliminates all occurrences of units
       in formula [f] using algebraic unit laws. *)
   let rec elim_units : form -> form = function
     (* Absorbing elements *)
     | FConn (`And, [ _; FFalse ])
     | FConn (`And, [ FFalse; _ ])
     | FConn (`Not, [ FTrue ])
     | FBind (`Exist, _, _, FFalse) ->
         Form.f_false
     (* | FPred ("_EQ", [e1; e2]) when Form.e_equal e1 e2 ->
         Form.f_true *)
     | FConn (`Or, [ _; FTrue ])
     | FConn (`Or, [ FTrue; _ ])
     | FConn (`Imp, [ _; FTrue ])
     | FConn (`Imp, [ FFalse; _ ])
     | FConn (`Not, [ FFalse ])
     | FBind (`Forall, _, _, FTrue) ->
         Form.f_true
     (* Neutral elements *)
     | FConn (`And, [ f; FTrue ])
     | FConn (`And, [ FTrue; f ])
     | FConn (`Or, [ f; FFalse ])
     | FConn (`Or, [ FFalse; f ])
     | FConn (`Imp, [ FTrue; f ])
     | FConn (`Equiv, [ FTrue; f ])
     | FConn (`Equiv, [ f; FTrue ]) ->
         elim_units f
     | (FTrue | FFalse | FPred _) as f -> f
     | FConn (c, fs) as f ->
         let fs' = List.map elim_units fs in
         if fs = fs' then f else elim_units (FConn (c, fs'))
     | FBind (b, x, ty, f1) as f ->
         let f1' = elim_units f1 in
         if f1 = f1' then f else elim_units (FBind (b, x, ty, f1'))

   (** Compute a debug representation of a linkage between formulas. *)
   let show_linkage env (mode : [ `Backward | `Forward ]) ((l, _), (r, _)) =
     let op = match mode with `Backward -> "⊢" | `Forward -> "∗" in
     Printf.sprintf "%s %s %s"
       (Notation.f_tostring env l)
       op
       (Notation.f_tostring env r)

   (** [well_scoped goal lenv e] returns [true] if all variables in the
       expression [e] are bound either in the global environment [goal.g_env],
       or in the local environment [lenv]. *)
   let well_scoped goal ctx e =
     e_vars e
     |> List.for_all
          begin
            fun x -> fc_is_bound x ctx || Vars.exists goal.g_env (fc_exit x ctx)
          end

   (** [instantiable goal lenv ctx s x] returns [true] if the variable [x] is
       either flex, or bound in substitution [s] to an expression [e] which is
       well-scoped. *)
   let instantiable goal lenv ctx s x ty =
     let lenv = LEnv.enter lenv x ty in
     match get_tag (x, LEnv.get_index lenv x) s with
     | Some (Sbound e) -> well_scoped goal ctx e
     | Some Sflex -> true
     | None -> false

   let invertible (kind : [ `Left | `Right | `Forward ]) (f : form) : bool =
     match kind with
     (* Right invertible *)
     | `Right -> begin
         match f with
         | FConn (c, _) -> begin
             match c with `Imp | `Not | `Equiv -> true | _ -> false
           end
         | FBind (`Forall, _, _, _) -> true
         | _ -> false
       end
     (* Left invertible *)
     | `Left -> begin
         match f with
         | FConn (c, _) -> begin match c with `Or -> true | _ -> false end
         | FBind (`Exist, _, _, _) -> true
         | _ -> false
       end
     (* Forward invertible *)
     | `Forward -> begin
         match f with
         | FConn (c, _) -> begin match c with _ -> false end
         | FBind (`Exist, _, _, _) -> true
         | _ -> false
       end

   let no_prio kind ((f, sub) : form * int list) =
     let inv = invertible kind f in
     (not inv) || List.is_empty sub

   (** This function is a horrible mess and should be refactored.
       Some tests would also be a great idea : I encountered weird bugs in here. *)
   let dlink ((src, dst) : link)
       ((s_src, s_dst) : Form.Subst.subst * Form.Subst.subst) (proof : Proof.proof)
       : itrace =
     let { g_pregoal = goal; _ }, item_src, (sub_src, t_src) =
       IPath.destr proof src
     in
     let _, item_dst, (sub_dst, t_dst) = IPath.destr proof dst in

     begin
       match (t_src, t_dst) with
       | `F _, `E _ | `E _, `F _ -> raise Tactics.TacticNotApplicable
       | _ -> ()
     end;

     (* I had to refactor [backward_core] out of [backward] to "fix" a very weird bug
        involving pattern matching. It might be related to the following compiler bug :
        https://github.com/ocaml/ocaml/issues/7241 *)
     let backward_core (ctx : fctx)
         (s : ((LEnv.lenv * subst) * (LEnv.lenv * subst)) ref)
         (switch_pol : bool ref)
         ((((l, lsub) as h), ((r, rsub) as c)) as linkage :
           (form * int list) * (form * int list)) =
       let ((env1, s1) as es1), ((env2, s2) as es2) = !s in
       begin
         match linkage with
         (* Right rules *)

         (* R∧s *)
         | _, (FConn (`And, fs), i :: sub) when no_prio `Left h -> begin
             try
               let fi, fs = List.pop_at i fs in
               (Some (CConn (`And, fs, i)), (1, None), (h, (fi, sub)))
             with Not_found -> failwith "empty conjunction"
           end
         (* R∨ *)
         | _, (FConn (`Or, fs), i :: sub) when no_prio `Left h -> begin
             try
               let fi, fs = List.pop_at i fs in
               (Some (CConn (`Or, fs, i)), (1, None), (h, (fi, sub)))
             with Not_found -> failwith "empty disjunction"
           end
         (* R⇒₁ *)
         | _, (FConn (`Imp, [ f1; f2 ]), 0 :: sub) ->
             switch_pol := true;
             (Some (CConn (`Imp, [ f2 ], 0)), (1, None), (h, (f1, sub)))
         (* R⇒₂ *)
         | _, (FConn (`Imp, [ f1; f2 ]), 1 :: sub) ->
             (Some (CConn (`Imp, [ f1 ], 1)), (1, None), (h, (f2, sub)))
         (* R¬ *)
         | _, (FConn (`Not, [ f1 ]), 0 :: sub) ->
             switch_pol := true;
             (Some (CConn (`Not, [], 0)), (1, None), (h, (f1, sub)))
         | _, (FConn (`Equiv, [ _; _ ]), _) ->
             failwith "DnD on positive equivalence currently unsupported"
         | _, (FBind (`Exist, x, ty, f1), 0 :: sub)
           when no_prio `Left h && instantiable goal env2 ctx s2 x ty ->
             let env2 = LEnv.enter env2 x ty in
             s := (es1, (env2, s2));
             begin
               match get_tag (x, LEnv.get_index env2 x) s2 with
               (* R∃i *)
               | Some (Sbound e) ->
                   let f1 = Subst.f_apply1 (x, 0) e f1 in
                   (None, (1, Some (env1, env2, e)), (h, (f1, sub)))
               (* R∃s *)
               | Some Sflex ->
                   s := (es1, (env2, s2));
                   let h = (f_shift (x, 0) l, lsub) in
                   (Some (CBind (`Exist, x, ty)), (1, None), (h, (f1, sub)))
               | None -> assert false
             end
         (* R∀s *)
         | _, (FBind (`Forall, x, ty, f1), 0 :: sub) ->
             s := (es1, (LEnv.enter env2 x ty, s2));
             let h = (f_shift (x, 0) l, lsub) in
             (Some (CBind (`Forall, x, ty)), (1, None), (h, (f1, sub)))
         (* Left rules *)
         (* L∧ *)
         | (FConn (`And, fs), i :: sub), _ when no_prio `Right c -> begin
             try (None, (0, None), ((List.at fs i, sub), c))
             with Invalid_argument _ -> failwith "empty conjunction"
           end
         (* L∨ *)
         | (FConn (`Or, fs), i :: sub), _ -> begin
             try
               let fi, fs = List.pop_at i fs in
               let fs = List.map (fun fj -> f_imp fj r) fs in
               (Some (CConn (`And, fs, i)), (0, None), ((fi, sub), c))
             with Not_found -> failwith "empty disjunction"
           end
         (* L⇒₂ *)
         | (FConn (`Imp, [ f1; f2 ]), 1 :: sub), _ when no_prio `Right c ->
             (Some (CConn (`And, [ f1 ], 1)), (0, None), ((f2, sub), c))
         (* L⇔₁ *)
         | (FConn (`Equiv, [ f1; f2 ]), 0 :: sub), _ when no_prio `Right c ->
             (Some (CConn (`And, [ f2 ], 0)), (0, None), ((f1, sub), c))
         (* L⇔₂ *)
         | (FConn (`Equiv, [ f1; f2 ]), 1 :: sub), _ when no_prio `Right c ->
             (Some (CConn (`And, [ f1 ], 1)), (0, None), ((f2, sub), c))
         (* L∃s *)
         | (FBind (`Exist, x, ty, f1), 0 :: sub), _ ->
             s := ((LEnv.enter env1 x ty, s1), es2);
             let c = (f_shift (x, 0) r, rsub) in
             (Some (CBind (`Forall, x, ty)), (0, None), ((f1, sub), c))
         | (FBind (`Forall, x, ty, f1), 0 :: sub), _
           when no_prio `Right c && instantiable goal env1 ctx s1 x ty ->
             let env1 = LEnv.enter env1 x ty in
             s := ((env1, s1), es2);
             begin
               match get_tag (x, LEnv.get_index env1 x) s1 with
               (* L∀i *)
               | Some (Sbound e) ->
                   let f1 = f_apply1 (x, 0) e f1 in
                   (None, (0, Some (env1, env2, e)), ((f1, sub), c))
               (* L∀s *)
               | Some Sflex ->
                   s := ((env1, s1), es2);
                   let c = (f_shift (x, 0) r, rsub) in
                   (Some (CBind (`Exist, x, ty)), (0, None), ((f1, sub), c))
               | None -> assert false
             end
         | _ -> raise Tactics.TacticNotApplicable
       end
     in

     let rec backward (ctx : fctx) (itrace : itrace)
         (s : (LEnv.lenv * subst) * (LEnv.lenv * subst))
         (((l, _), (r, rsub)) as linkage : (form * int list) * (form * int list)) :
         form * itrace =
       (*js_log (Subst.to_string (s |> fst |> snd) ^ " ⊢ " ^ Subst.to_string (s |> snd |> snd));*)
       js_log (show_linkage goal.g_env `Backward linkage);

       match linkage with
       (* End rules *)
       | (_, []), (_, []) ->
           let f =
             begin
               match (l, r) with
               (* Bid *)
               | _ when f_equal goal.g_env l r -> f_true
               | FPred (c1, ts1), FPred (c2, ts2) when c1 = c2 ->
                   List.fold_left2
                     (fun f t1 t2 -> f_and f (FPred ("_EQ", [ t1; t2 ])))
                     f_true ts1 ts2
               (* Brel *)
               | _ -> f_imp l r
             end
           in
           (fc_fill f (fc_rev ctx), itrace)
       | (FPred ("_EQ", [ e1; e2 ]), [ i ]), (FPred _, _)
         when e_equal_delta goal.g_env
                (subexpr (`F r) rsub)
                (if i = 0 then e1 else e2) ->
           let res =
             (* L=₁ *)
             if i = 0 then e2 (* L=₂ *) else e1
           in
           let f = rewrite_subterm (`E res) (`F r) rsub |> form_of_term in
           (fc_fill f (fc_rev ctx), itrace)
       (* Commuting rules *)
       | _ ->
           let switch_pol = ref false in
           let s = ref s in

           let ( (ictx : ifctx option)
               , (choice : choice)
               , (linkage : (form * int list) * (form * int list)) ) =
             backward_core ctx s switch_pol linkage
           in
           let cont = if !switch_pol then forward ~side:1 else backward in
           let ctx = match ictx with Some i -> i :: ctx | None -> ctx in
           cont ctx (choice :: itrace) !s linkage
     and forward (ctx : fctx) (itrace : itrace) ?(side = 1)
         ((((env1, _) as es1), ((env2, s2) as es2)) as s :
           (LEnv.lenv * subst) * (LEnv.lenv * subst))
         ((((l, lsub) as h), (r, rsub)) as linkage :
           (form * int list) * (form * int list)) : form * itrace =
       js_log (show_linkage goal.g_env `Forward linkage);

       match linkage with
       (* End rules *)
       | (_, []), (_, []) ->
           let f =
             begin
               match (l, r) with
               (* Fid *)
               | _ when f_equal goal.g_env l r -> l
               (* Frel *)
               | _ -> f_and l r
             end
           in
           (fc_fill f (fc_rev ctx), itrace)
       | (FPred ("_EQ", [ e1; e2 ]), [ i ]), (FPred _, _)
         when e_equal_delta goal.g_env
                (subexpr (`F r) rsub)
                (if i = 0 then e1 else e2) ->
           let res =
             (* L=₁ *)
             if i = 0 then e2 (* L=₂ *) else e1
           in
           let f = rewrite_subterm (`E res) (`F r) rsub |> form_of_term in
           (fc_fill f (fc_rev ctx), itrace)
       (* Commuting rules *)
       | _ ->
           let switch_pol = ref false in
           let s = ref s in
           let new_side = ref side in
           let witness = ref None in

           let ( (ictx : ifctx option)
               , (linkage : (form * int list) * (form * int list)) ) =
             begin
               match linkage with
               (* F∧ *)
               | _, (FConn (`And, fs), i :: sub) -> begin
                   try (None, (h, (List.at fs i, sub)))
                   with Not_found -> failwith "empty conjunction"
                 end
               (* F∨ *)
               | _, (FConn (`Or, fs), i :: sub) when no_prio `Forward h -> begin
                   try
                     let fi, fs = List.pop_at i fs in
                     (Some (CConn (`Or, fs, i)), (h, (fi, sub)))
                   with Not_found -> failwith "empty disjunction"
                 end
               (* F⇒₁ *)
               | _, (FConn (`Imp, [ f1; f2 ]), 0 :: sub) when no_prio `Forward h ->
                   switch_pol := true;
                   (Some (CConn (`Imp, [ f2 ], 0)), (h, (f1, sub)))
               (* F⇒₂ *)
               | _, (FConn (`Imp, [ f1; f2 ]), 1 :: sub) when no_prio `Forward h ->
                   (Some (CConn (`Imp, [ f1 ], 1)), (h, (f2, sub)))
               (* F¬ *)
               | _, (FConn (`Not, [ f1 ]), 0 :: sub) when no_prio `Forward h ->
                   switch_pol := true;
                   (Some (CConn (`Not, [], 0)), (h, (f1, sub)))
               (* F⇔₁ *)
               | _, (FConn (`Equiv, [ f1; f2 ]), 0 :: sub) when no_prio `Forward h
                 ->
                   switch_pol := true;
                   (Some (CConn (`Imp, [ f2 ], 0)), (h, (f1, sub)))
               (* F⇔₂ *)
               | _, (FConn (`Equiv, [ f1; f2 ]), 1 :: sub) when no_prio `Forward h
                 ->
                   switch_pol := true;
                   (Some (CConn (`Imp, [ f1 ], 0)), (h, (f2, sub)))
               (* F∃s *)
               | _, (FBind (`Exist, x, ty, f1), 0 :: sub) ->
                   s := (es1, (LEnv.enter env2 x ty, s2));
                   let h = (f_shift (x, 0) l, lsub) in
                   (Some (CBind (`Exist, x, ty)), (h, (f1, sub)))
               | _, (FBind (`Forall, x, ty, f1), 0 :: sub)
                 when no_prio `Forward h && instantiable goal env2 ctx s2 x ty ->
                   let env2 = LEnv.enter env2 x ty in
                   s := (es1, (env2, s2));
                   begin
                     match get_tag (x, LEnv.get_index env2 x) s2 with
                     (* F∀i *)
                     | Some (Sbound e) ->
                         let f1 = Subst.f_apply1 (x, 0) e f1 in
                         witness :=
                           if side = 1
                           then Some (env1, env2, e)
                           else Some (env2, env1, e);
                         (None, (h, (f1, sub)))
                     (* F∀s *)
                     | Some Sflex ->
                         s := (es1, (LEnv.enter env2 x ty, s2));
                         let h = (f_shift (x, 0) l, lsub) in
                         (Some (CBind (`Forall, x, ty)), (h, (f1, sub)))
                     | None -> assert false
                   end
               (* Fcomm *)
               | h, h' ->
                   s := (es2, es1);
                   new_side := 1 - side;
                   (None, (h', h))
             end
           in
           let cont = if !switch_pol then backward else forward ~side:!new_side in
           let ctx = match ictx with Some i -> i :: ctx | None -> ctx in
           let itrace =
             if !new_side <> side then itrace else (!new_side, !witness) :: itrace
           in
           cont ctx itrace !s linkage
     in

     let _, itrace =
       match ((item_src, sub_src, s_src), (item_dst, sub_dst, s_dst)) with
       | (`H (hid, { h_form = h; _ }), subh, sh), (`C c, subc, sc)
       | (`C c, subc, sc), (`H (hid, { h_form = h; _ }), subh, sh) ->
           let form, itrace =
             backward [] []
               ((LEnv.empty, sh), (LEnv.empty, sc))
               ((h, subh), (c, subc))
           in
           (([ (Some hid, []) ], form |> elim_units), itrace)
       | ( (`H (hid, { h_form = h; _ }), subh, s)
         , (`H (hid', { h_form = h'; _ }), subh', s') ) ->
           let form, itrace =
             forward [] []
               ((LEnv.empty, s), (LEnv.empty, s'))
               ((h, subh), (h', subh'))
           in
           ( ([ (Some hid, []); (Some hid', [ form |> elim_units ]) ], goal.g_goal)
           , itrace )
       | _ -> raise Tactics.TacticNotApplicable
     in
     List.rev itrace
*)
