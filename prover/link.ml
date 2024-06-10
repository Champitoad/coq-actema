open Utils.Pervasive
open Api
open Lang
open Logic
open ProverLogic

type link = Path.t * Path.t [@@deriving show]
type hyperlink = Path.t list * Path.t list [@@deriving show]

type linkaction =
  | Nothing
  | Both of linkaction * linkaction
  | Subform of FVarId.t list * FVarId.t list * Unif.subst
    (*| Instantiate of Term.t * Path.t
      | Rewrite of Term.t * Term.t * Path.t list
      | Fold of Name.t * Path.t list
      | Unfold of Name.t * Path.t list*)
[@@deriving show]

let hyperlink_of_link : link -> hyperlink = fun (src, dst) -> ([ src ], [ dst ])

let rec remove_nothing action =
  match action with
  | Nothing -> None
  | Both (left, right) -> begin
      match (remove_nothing left, remove_nothing right) with
      | None, None -> None
      | Some left, None -> Some left
      | None, Some right -> Some right
      | Some left, Some right -> Some (Both (left, right))
    end
  | _ -> Some action

(** [traverse_rec env context  rigid_fvars fvars pol term sub] traverses [term] along the path [sub], 
    recording in [rigid_fvars] which variables are rigid, and returning the list of free variables 
    and the list of rigid variables.
    
    This assumes the path [sub] points to a sub-formula in the first-order skeleton + equality,
    and raises an exception if it doesn't. *)
let rec traverse_rec env context rigid_fvars fvars pol term sub :
    FVarId.t list * FVarId.t list * Context.t * Term.t =
  let fo = FirstOrder.view env context term in
  match (sub, fo) with
  | [], _ -> (rigid_fvars, List.rev fvars, context, term)
  (* Inverse the polarity. *)
  | 1 :: sub, FConn (Not, [ t1 ]) ->
      traverse_rec env context rigid_fvars fvars (Polarity.opp pol) t1 sub
  | 0 :: sub, FImpl (t1, t2) ->
      traverse_rec env context rigid_fvars fvars (Polarity.opp pol) t1 sub
  (* Recurse in the formula. *)
  | 1 :: sub, FImpl (t1, t2) ->
      traverse_rec env context rigid_fvars fvars pol t2 sub
  | i :: sub, FConn (conn, ts) when 1 <= i && i <= List.length ts ->
      traverse_rec env context rigid_fvars fvars pol (List.at ts (i - 1)) sub
  (* Binders. *)
  | 1 :: sub, FBind (Forall, x, ty, body) ->
      let fvar, context = Context.add_fresh x ty context in
      let body = Term.instantiate fvar body in
      let rigid_fvars =
        match pol with
        | Polarity.Pos | Polarity.Sup -> fvar :: rigid_fvars
        | _ -> rigid_fvars
      in
      traverse_rec env context rigid_fvars (fvar :: fvars) pol body sub
  | 2 :: 1 :: sub, FBind (Exist, x, ty, body) ->
      let fvar, context = Context.add_fresh x ty context in
      let body = Term.instantiate fvar body in
      let rigid_fvars =
        match pol with
        | Polarity.Neg | Polarity.Sup -> fvar :: rigid_fvars
        | _ -> rigid_fvars
      in
      traverse_rec env context rigid_fvars (fvar :: fvars) pol body sub
  (* Equality. *)
  | [ 2 ], FAtom (App (_, Cst eq, [ _; t1; t2 ]))
    when Name.equal eq Constants.eq ->
      (rigid_fvars, List.rev fvars, context, t2)
  | [ 3 ], FAtom (App (_, Cst eq, [ _; t1; t2 ]))
    when Name.equal eq Constants.eq ->
      (rigid_fvars, List.rev fvars, context, t2)
  (* The path is either invalid or escapes the first-order skeleton. *)
  | _ -> raise @@ InvalidSubtermPath (term, sub)

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
  | App (_, f1, args1), App (_, f2, args2) ->
      List.exists (not_unifiable_fast depth)
      @@ List.combine (f1 :: args1) (f2 :: args2)
  | Lambda (_, x1, ty1, body1), Lambda (_, x2, ty2, body2)
  | Prod (_, x1, ty1, body1), Prod (_, x2, ty2, body2) ->
      not_unifiable_fast depth (ty1, ty2)
      || not_unifiable_fast (depth + 1) (body1, body2)
  | _ -> true

(*******************************************************************************************)
(* Link predicates. *)

module Pred = struct
  type lpred = Proof.t -> link -> linkaction list
  type hlpred = Proof.t -> hyperlink -> linkaction list

  let lift : lpred -> hlpred =
   fun pred proof -> function
    | [ src ], [ dst ] -> pred proof (src, dst)
    | _ -> []

  (** [mult2 pred1 pred2] sort-circuits : if [pred1] return an empty list, 
      [pred2] is not evaluated. *)
  let mult2 pred1 pred2 : hlpred =
   fun proof link ->
    let open Utils.Monad.List in
    let* act1 = pred1 proof link in
    let* act2 = pred2 proof link in
    return @@ Both (act1, act2)

  (** [mult preds] evaluates the predicates in [preds] from left to right, 
      and stops as soon as one predicate returns an empty list. *)
  let mult preds : hlpred =
    match preds with
    | [] -> fun proof link -> []
    | p0 :: preds -> List.fold_left mult2 p0 preds

  let add : hlpred list -> hlpred =
   fun ps pr lnk -> List.map (fun p -> p pr lnk) ps |> List.concat

  let if_empty : hlpred -> hlpred -> hlpred =
   fun p1 p2 pr lnk ->
    let actions = p1 pr lnk in
    if not (List.is_empty actions) then actions else p2 pr lnk

  (** This should be fast. *)
  let pre_unifiable : lpred =
   fun proof (src, dst) ->
    try
      let src_term = Logic.term_of_item @@ PathUtils.item src proof in
      let dst_term = Logic.term_of_item @@ PathUtils.item dst proof in
      let not_unif =
        not_unifiable_fast 0
          (subterm_raw src_term src.sub, subterm_raw dst_term dst.sub)
      in
      if not_unif
      then (* These terms are definitely not unifiable. *) []
      else (* We still don't known. *) [ Nothing ]
    with InvalidSubtermPath _ | Invalid_argument _ -> []

  let unifiable : lpred =
   fun proof (src, dst) ->
    try
      (* Now the actual unification. *)
      let goal, src_item, _, _ = PathUtils.destr src proof in
      let _, dst_item, _, _ = PathUtils.destr dst proof in
      let env = goal.g_pregoal.g_env in

      let src_rigid, src_fvars, context, src_subterm =
        traverse_rec env Context.empty [] []
          (Polarity.of_item src_item)
          (Logic.term_of_item src_item)
          src.sub
      in
      (* We reuse in [dst] the context we built for [src],
         to avoid clashes between free variables of [src] and [dst]. *)
      let dst_rigid, dst_fvars, context, dst_subterm =
        traverse_rec env context [] []
          (Polarity.of_item dst_item)
          (Logic.term_of_item dst_item)
          dst.sub
      in
      (* Unify the two subterms. *)
      (* TODO : add the forbidden dependencies. *)
      let subst =
        Unif.unify env context ~rigid_fvars:(src_rigid @ dst_rigid) src_subterm
          dst_subterm
      in

      (* Check there is a solution. *)
      match subst with
      | Some subst -> [ Subform (src_fvars, dst_fvars, subst) ]
      | None -> []
    with InvalidSubtermPath _ | Invalid_argument _ ->
      (* We got an exception : most likely [traverse_rec] raised an exception because a path was invalid. *)
      []

  let opposite_pol_formulas : lpred =
   fun proof (src, dst) ->
    try
      let src_pol = Polarity.of_ipath proof src in
      let dst_pol = Polarity.of_ipath proof dst in
      match (src_pol, dst_pol) with
      | Neg, Pos | Pos, Neg | Sup, _ | _, Sup -> [ Nothing ]
      | _ -> []
    with Invalid_argument _ | InvalidSubtermPath _ -> []

  let neg_eq_operand : lpred =
   fun proof (src, dst) ->
    let check (path : Path.t) : bool =
      try
        let eq_sub = List.remove_at (List.length path.sub - 1) path.sub in
        let goal, item, _, _ = PathUtils.destr path proof in
        let env = goal.g_pregoal.g_env in

        match
          Polarity.of_subterm env (Polarity.of_item item) (term_of_item item)
            eq_sub
        with
        (* TODO: should we also allow the [Sup] polarity ? *)
        | Neg, _, App (_, Cst eq, [ _; _; _ ]) when Name.equal eq Constants.eq
          ->
            true
        | _ -> false
      with Invalid_argument _ | InvalidSubtermPath _ -> false
    in
    if check src || check dst then [ Nothing ] else []

  let intuitionistic : lpred =
   fun proof (src, dst) ->
    let neg_count (path : Path.t) : int =
      let goal, item, _, _ = PathUtils.destr path proof in
      let negs =
        Polarity.neg_count goal.g_pregoal.g_env (term_of_item item) path.sub
      in
      match item with
      | Concl _ -> negs
      | Hyp _ -> negs + 1
      | Var _ ->
          raise
          @@ Invalid_argument "Link.intuitionistic : expected a formula item"
    in

    try
      match (neg_count src, neg_count dst) with
      | m, n when (m > 0 && n > 0) || (m = 0 && n <= 1) || (m <= 1 && n = 0) ->
          [ Nothing ]
      | _ -> []
    with InvalidSubtermPath _ | Invalid_argument _ -> []

  let wf_subform : hlpred =
    mult
      [ lift pre_unifiable
      ; lift opposite_pol_formulas
      ; lift intuitionistic
      ; lift unifiable
      ]

  (* A deep rewrite link is not required to be intuitionistic. *)
  let deep_rewrite : hlpred =
    mult [ lift pre_unifiable; lift neg_eq_operand; lift unifiable ]

  let instantiate : hlpred =
   fun proof (src, dst) -> failwith "instantiate: todo"
  (*let is_free_expr (t : term) (sub : int list) : bool =
      let lenv, subt =
        List.fold_left
          (fun (lenv, t) i ->
            let lenv =
              match t with
              | `F (FBind (_, x, ty, _)) -> LEnv.enter lenv x ty
              | _ -> lenv
            in
            let t = direct_subterm t i in
            (lenv, t))
          (LEnv.empty, t) sub
      in
      match subt with
      | `F _ -> false
      | `E e -> List.for_all (not <<| LEnv.exists lenv) (e_vars e)
    in

    fun proof (srcs, dsts) ->
      (* Link to quantified subformula *)
      let to_form p_wit p_form =
        let Proof.{ g_pregoal = goal; _ }, item_wit, (sub_wit, wit) =
          IPath.destr proof p_wit
        in

        let where = match p_wit.ctxt.kind with `Var w -> w | _ -> `Body in
        let ctxt_wit = term_of_item ~where item_wit in

        (* Check that the witness contains only free variables *)
        if is_free_expr ctxt_wit sub_wit
        then
          let pol = Polarity.of_ipath proof p_form in
          let f = IPath.term proof p_form in

          let wit = expr_of_term wit in
          let ty_wit = Form.einfer goal.g_env wit in

          (* Check that the quantifier is instantiable, meaning it has
             the right polarity as well as the same type as the witness *)
          match (pol, f) with
          | Neg, `F (FBind (`Forall, _, ty, _))
          | Pos, `F (FBind (`Exist, _, ty, _))
            when Form.t_equal goal.g_env ty ty_wit ->
              [ `Instantiate (wit, p_form) ]
          | _ -> []
        else []
      in

      (* Link to quantified occurrences *)
      match (srcs, dsts) with
      | [ src ], [ dst ] -> begin
          match pair_map (IPath.term proof) (src, dst) with
          | `E _, `F _ -> to_form src dst
          | `F _, `E _ -> to_form dst src
          | `E _, `E _ -> [] (* TODO *)
          | _ -> []
        end
      | _ -> []*)

  let rewrite : hlpred = fun proof lnk -> failwith "rewrite: todo"
  (*let rewrite_data (p : IPath.t) =
      if p.ctxt.kind = `Hyp
      then
        let _, it, _ = IPath.destr proof p in
        match (p.sub, form_of_item it) with
        | [ 0 ], FPred ("_EQ", [ red; res ]) | [ 1 ], FPred ("_EQ", [ res; red ])
          ->
            Some (red, res)
        | _ -> None
      else None
    in

    try
      match (lnk, pair_map (List.hd |>> rewrite_data) lnk) with
      (* If it is a simple link where both ends are sides of equalities,
         disambiguate by rewriting into the destination *)
      | ([ _ ], [ dst ]), (Some (red, res), Some _) ->
          [ `Rewrite (red, res, [ dst ]) ]
      | ([ _ ], tgts), (Some (red, res), _) | (tgts, [ _ ]), (_, Some (red, res))
        ->
          if List.exists (fun p -> p.IPath.ctxt.kind = `Var `Head) tgts
          then []
          else [ `Rewrite (red, res, tgts) ]
      | _ -> []
      (* Empty link end *)
    with Failure _ -> []*)

  let fold : hlpred = fun proof lnk -> failwith "fold: todo"
  (*let fold_data (p : IPath.t) =
      let _, it, _ = IPath.destr proof p in
      match (it, p.ctxt.kind, p.sub) with
      | `V (x, (_, Some _)), `Var where, [] -> Some (x, where)
      | _ -> None
    in

    try
      match (lnk, pair_map (List.hd |>> fold_data) lnk) with
      (* If it is a simple link where both ends are variable bodies,
         disambiguate by folding in the destination *)
      | ([ _ ], [ dst ]), (Some (x, `Body), Some (_, `Body)) ->
          [ `Fold (x, [ dst ]) ]
      | ([ p ], tgts), (Some (x, where), _) | (tgts, [ p ]), (_, Some (x, where))
        ->
          let is_head p = p.IPath.ctxt.kind = `Var `Head in
          if where = `Head
          then if List.exists is_head tgts then [] else [ `Unfold (x, tgts) ]
          else begin
            match List.filter is_head tgts with
            | [ p' ] ->
                Option.map_default
                  (fun (y, _) -> [ `Unfold (y, p :: List.remove tgts p') ])
                  [] (fold_data p')
            | [] -> [ `Fold (x, tgts) ]
            | _ :: _ :: _ -> []
          end
      | _ -> []
      (* Empty link end *)
    with Failure _ -> []*)
end
