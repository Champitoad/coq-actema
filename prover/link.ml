open Utils.Pervasive
open Api
open Lang
open Logic
open ProverLogic

type link = Path.t * Path.t [@@deriving show]
type hyperlink = Path.t list * Path.t list [@@deriving show]

let hyperlink_of_link : link -> hyperlink = fun (src, dst) -> ([ src ], [ dst ])

(** [traverse_rec env context  rigid_fvars fvars pol term sub] traverses [term] along the path [sub], 
    recording in [rigid_fvars] which variables are rigid, and returning the list of free variables 
    and the list of rigid variables (topmost first).
    
    This assumes the path [sub] points to a sub-formula in the first-order skeleton + equality,
    and raises an exception if it doesn't. *)
let rec traverse_rec env context rigid_fvars fvars pol term sub :
    FVarId.t list * FVarId.t list * Context.t * Term.t =
  let ret t = (List.rev rigid_fvars, List.rev fvars, context, t) in
  match (sub, FirstOrder.view env context term) with
  | [], _ -> ret term
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
      ret t1
  | [ 3 ], FAtom (App (_, Cst eq, [ _; t1; t2 ]))
    when Name.equal eq Constants.eq ->
      ret t2
  (* The path is either invalid or escapes the first-order skeleton. *)
  | _ -> raise @@ InvalidSubtermPath (term, sub)

(** [consecutive_pairs [x0; x1; x2; ... ]] returns the list [(x0, x1); (x1; x2); (x2, x3); ...]. *)
let consecutive_pairs (xs : 'a list) : ('a * 'a) list =
  let rec loop = function
    | [] | [ _ ] -> []
    | x1 :: x2 :: xs -> (x1, x2) :: loop (x2 :: xs)
  in
  loop xs

(*******************************************************************************************)
(* Link predicates. *)

module Pred = struct
  (* Instantiate the monad. *)
  include Utils.Monad.MakePlus (struct
    type 'a t = Proof.t -> hyperlink -> 'a option

    let return x _ _ = Some x

    let bind x f proof hyperlink =
      let open Utils.Monad.Option in
      let* x' = x proof hyperlink in
      f x' proof hyperlink

    let mzero _ _ = None

    let mplus x y proof hyperlink =
      let open Utils.Monad.Option in
      x proof hyperlink <|> y proof hyperlink
  end)

  (** Simply read the proof. Always succeeds. *)
  let ask_proof : Proof.t t = fun proof _ -> Some proof

  (** Simply read the hyperlink. Always succeeds. *)
  let ask_hyperlink : hyperlink t = fun proof hyperlink -> Some hyperlink

  let fail = mzero

  (** Check if the hyperlink is of the form [([src], [dst])] and return [(src, dst)]. *)
  let ask_link : link t =
    let* hyperlink = ask_hyperlink in
    match hyperlink with [ src ], [ dst ] -> return (src, dst) | _ -> fail

  let unifiable : unif_data t =
    let* proof = ask_proof in
    let* src, dst = ask_link in
    try
      (* The actual unification. *)
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
      let subst =
        Unif.unify env context
          ~forbidden_deps:
            (consecutive_pairs src_fvars @ consecutive_pairs dst_fvars)
          ~rigid_fvars:(src_rigid @ dst_rigid) src_subterm dst_subterm
      in

      (* Check there is a solution. *)
      match subst with
      | Some subst ->
          return { context; subst; fvars_1 = src_fvars; fvars_2 = dst_fvars }
      | None -> fail
    with InvalidSubtermPath _ | Invalid_argument _ ->
      (* We got an exception : most likely [traverse_rec] raised an exception because a path was invalid. *)
      fail

  let opposite_pol_formulas : unit t =
    let* proof = ask_proof in
    let* src, dst = ask_link in
    try
      let src_pol = Polarity.of_ipath proof src in
      let dst_pol = Polarity.of_ipath proof dst in
      match (src_pol, dst_pol) with
      | Neg, Pos | Pos, Neg | Sup, _ | _, Sup -> return ()
      | _ -> fail
    with Invalid_argument _ | InvalidSubtermPath _ -> fail

  let neg_eq_operand : [ `Left | `Right ] t =
    let* proof = ask_proof in
    let* src, dst = ask_link in
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
    if check src
    then return `Left
    else if check dst
    then return `Right
    else fail

  let intuitionistic : unit t =
    let* proof = ask_proof in
    let* src, dst = ask_link in
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
          return ()
      | _ -> fail
    with InvalidSubtermPath _ | Invalid_argument _ -> fail

  let wf_subform : Logic.action t =
    let* src, dst = ask_link in
    let* () = opposite_pol_formulas in
    let* () = intuitionistic in
    let* unif = unifiable in
    return @@ ADnD (src, dst, unif, Subform)

  (* A deep rewrite link is not required to be intuitionistic. *)
  let deep_rewrite : Logic.action t =
    let* src, dst = ask_link in
    let* side = neg_eq_operand in
    let* unif = unifiable in
    match side with
    | `Left -> return @@ ADnD (src, dst, unif, RewriteL)
    | `Right -> return @@ ADnD (src, dst, unif, RewriteR)

  let instantiate proof (src, dst) = failwith "instantiate: todo"
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

  let rewrite proof link = failwith "rewrite: todo"
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

  let fold proof link = failwith "fold: todo"
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
