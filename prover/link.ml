open Utils.Pervasive
open Api
open Lang
open Logic
open CoreLogic

type link = Path.t * Path.t [@@deriving show]
type hyperlink = Path.t list * Path.t list [@@deriving show]

type linkaction =
  | Nothing
  | Both of linkaction * linkaction
  | Subform of Unif.subst
  | Instantiate of Term.t * Path.t
  | Rewrite of Term.t * Term.t * Path.t list
  | Fold of Name.t * Path.t list
  | Unfold of Name.t * Path.t list
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

(** [traverse_rec pol acc fo sub] traverses [term] along the path [sub], 
    and recording an [SFlex] or [SRigid] sitem for each binder we cross.
    This assumes the path [sub] points to a sub-formula in the first-order skeleton,
    and raises an exception if it doesn't. *)
let rec traverse_rec pol acc (fo : FirstOrder.t) sub : Unif.sitem list =
  let open Unif in
  match (sub, fo) with
  | [], _ -> acc
  (* Inverse the polarity. *)
  | 1 :: sub, FConn (Not, [ t1 ]) -> traverse_rec (Polarity.opp pol) acc t1 sub
  | 0 :: sub, FImpl (t1, t2) -> traverse_rec (Polarity.opp pol) acc t1 sub
  (* Recurse in the formula. *)
  | 1 :: sub, FImpl (t1, t2) -> traverse_rec pol acc t2 sub
  | i :: sub, FConn (conn, ts) when 1 <= i && i <= List.length ts ->
      traverse_rec pol acc (List.at ts (i - 1)) sub
  (* Binders. *)
  | 1 :: sub, FBind (Forall, x, ty, body) ->
      let sitem = if pol = Polarity.Neg then SFlex else SRigid in
      traverse_rec pol (sitem :: acc) body sub
  | 2 :: 1 :: sub, FBind (Exist, x, ty, body) ->
      let sitem = if pol = Polarity.Pos then SFlex else SRigid in
      traverse_rec pol (sitem :: acc) body sub
  (* Equality. *)
  | [ 2 ], FAtom (App (Cst eq, [ _; _; _ ]))
  | [ 3 ], FAtom (App (Cst eq, [ _; _; _ ]))
    when Name.equal eq Name.eq ->
      acc
  (* The path is either invalid or escapes the first-order skeleton. *)
  | _ -> raise @@ InvalidSubtermPath (FirstOrder.to_term fo, sub)

(** [traverse path proof] traverses [path], deciding whether each traversed 
    binder is [SFlex] or [SRigid]. It returns the list of sitems computed,
    along with the subterm pointed at by [path]. 

    [path] should point to a something in the first-order skeleton,
    or to an argument of an equality which itself is in the first-order skeleton.
    
    @raise Path.InvalidPath if [path] is invalid.
    @raise Invalid_argument if [path] points to a variable item.
    @raise InvalidSubtermPath if [path] points to something outside the first-order skeleton. *)
let traverse (path : Path.t) (proof : Proof.t) :
    Unif.sitem list * Context.t * Term.t =
  let goal, item, context, subterm = PathUtils.destr path proof in
  let env = goal.g_pregoal.g_env in
  let fo_term = FirstOrder.of_term ~context env @@ term_of_item item in
  let sitems = traverse_rec (Polarity.of_item item) [] fo_term path.sub in
  (sitems, context, subterm)

(*******************************************************************************************)
(* Link predicates. *)

module Pred = struct
  type lpred = Proof.t -> link -> linkaction list
  type hlpred = Proof.t -> hyperlink -> linkaction list

  let lift : lpred -> hlpred =
   fun p pr -> function [ src ], [ dst ] -> p pr (src, dst) | _ -> []

  let mult : hlpred list -> hlpred =
    let aux : hlpred -> hlpred -> hlpred =
     fun p1 p2 pr lnk ->
      List.cartesian_product (p1 pr lnk) (p2 pr lnk)
      |> List.map (fun (a1, a2) -> Both (a1, a2))
    in
    List.fold_left aux (fun _ _ -> [ Nothing ])

  let add : hlpred list -> hlpred =
   fun ps pr lnk -> List.map (fun p -> p pr lnk) ps |> List.concat

  let if_empty : hlpred -> hlpred -> hlpred =
   fun p1 p2 pr lnk ->
    let actions = p1 pr lnk in
    if not (List.is_empty actions) then actions else p2 pr lnk

  (** This assumes that both sides of the link point to a formula in a hypothesis/conclusion. *)
  let unifiable : lpred =
   fun proof (src, dst) ->
    try
      let goal = PathUtils.goal src proof in

      (* Unify the two subterms. *)
      let solutions =
        Unif.unify goal.g_pregoal.g_env (traverse src proof)
          (traverse dst proof)
      in
      (* Get the first (acyclic) solution. *)
      match solutions () with
      (* The terms are unifiable. *)
      | Cons (subst, _) -> [ Subform subst ]
      (* The terms are not unifiable. *)
      | Nil -> []
    with InvalidSubtermPath _ | Invalid_argument _ | Path.InvalidPath _ ->
      (* We got an exception : most likely [traverse] raised an exception because a path was invalid. *)
      []

  let opposite_pol_formulas : lpred =
   fun proof (src, dst) ->
    try
      let src_pol = Polarity.of_ipath proof src in
      let dst_pol = Polarity.of_ipath proof dst in
      Format.printf "## %s ## %s ##\n" (Polarity.show src_pol)
        (Polarity.show dst_pol);
      match (src_pol, dst_pol) with
      | Neg, Pos | Pos, Neg | Sup, _ | _, Sup -> [ Nothing ]
      | _ -> []
    with Invalid_argument _ | InvalidSubtermPath _ | Path.InvalidPath _ -> []

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
        | Neg, _, App (Cst eq, [ _; _; _ ]) when Name.equal eq Name.eq -> true
        | _ -> false
      with Invalid_argument _ | InvalidSubtermPath _ | Path.InvalidPath _ ->
        false
    in
    if check src || check dst then [ Nothing ] else []

  let intuitionistic : lpred =
   fun proof (src, dst) -> failwith "intuitionistic: todo"
  (*let neg_count (p : IPath.t) =
      let _, it, (sub, _) = IPath.destr proof p in
      let f = form_of_item it in
      let n = Polarity.neg_count f sub in
      match it with
      | `C _ -> n
      | `H _ -> n + 1
      | `V _ -> raise (Invalid_argument "Expected a formula item")
    in

    try
      match (neg_count src, neg_count dst) with
      | m, n when (m > 0 && n > 0) || (m = 0 && n <= 1) || (m <= 1 && n = 0) ->
          [ `Nothing ]
      | _ -> []
    with InvalidSubFormPath _ | Invalid_argument _ -> []*)

  let wf_subform : hlpred =
    mult [ lift opposite_pol_formulas; lift unifiable; lift intuitionistic ]

  (* A deep rewrite link is not required to be intuitionistic. *)
  let deep_rewrite : hlpred = mult [ lift neg_eq_operand; lift unifiable ]

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

  let search_linkactions ?(fixed_srcs : Path.t list option)
      ?(fixed_dsts : Path.t list option) (hlp : hlpred) proof
      ((src, dst) : link) : (hyperlink * linkaction list) list =
    failwith "search_linkactions : todo"
  (*let subpath p sub =
      Path.{ goal = p.goal; kind = p.kind; sub = p.sub @ sub }
    in

    let query_actions lnk =
      match hlp proof lnk with
      | _ :: _ as actions -> [ (lnk, actions) ]
      | [] -> []
    in

    let open Monad.List in
    match (fixed_srcs, fixed_dsts) with
    | Some srcs, Some dsts -> query_actions (srcs, dsts)
    | Some srcs, None ->
        let _, _, _, t_dst = PathUtils.destr proof dst in
        t_subs t_dst >>= fun sub_dst ->
        query_actions (srcs, [ subpath dst sub_dst ])
    | None, Some dsts ->
        let _, _, (_, t_src) = PathUtils.destr proof src in
        t_subs t_src >>= fun sub_src ->
        query_actions ([ subpath src sub_src ], dsts)
    | None, None ->
        let _, _, (_, t_src) = PathUtils.destr proof src in
        let _, _, (_, t_dst) = PathUtils.destr proof dst in
        t_subs t_src >>= fun sub_src ->
        t_subs t_dst >>= fun sub_dst ->
        query_actions ([ subpath src sub_src ], [ subpath dst sub_dst ])*)
end
