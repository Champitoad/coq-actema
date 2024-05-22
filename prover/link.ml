open Utils
open Api
open Lang
open Logic
open CoreLogic

type link = Path.t * Path.t [@@deriving show]
type hyperlink = Path.t list * Path.t list [@@deriving show]

module IntGraph = Graph.Persistent.Digraph.Concrete (Int)

type sitem =
  | (* This variable is rigid : it cannot be substituted.
       In other terms it NOT a unification variable. *)
    SRigid
  | (* This variable is flexible : it can be substituted.
       In other it is a unification variable that has not been instantiated. *)
    SFlex
  | (* This variable is a unification variable that has been substituted.
       The term can still contain more [SFlex] of [Sbound] variables. *)
    SBound of Term.t
[@@deriving show]

let print_mapping fmt map =
  let bindings =
    IntMap.bindings map
    |> List.map (fun (var, item) ->
           Format.sprintf "(%d, %s)" var (show_sitem item))
  in
  Format.fprintf fmt "[%s]" (String.concat "," bindings)

type subst =
  { n_free_1 : int
  ; n_free_2 : int
  ; mapping : sitem IntMap.t [@printer print_mapping]
  ; deps : IntGraph.t [@opaque]
  }
[@@deriving show]

type linkaction =
  | Nothing
  | Both of linkaction * linkaction
  | Subform of subst
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

(*******************************************************************************************)
(* Unifying terms. *)

(** [unify_fast ] *)
let rec unify_fast 

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

  let unifiable : lpred = failwith "unifiable : todo"
  (*let open Form in
    let open PreUnif in
    fun proof (src, dst) ->
      try
        let deps, trav_src, trav_dst = traverse_link proof (src, dst) in

        let goal, _, (_, t_src) = IPath.destr proof src in
        let _, _, (_, t_dst) = IPath.destr proof dst in

        let s1 = Subst.aslist trav_src.subst in
        let s2 = Subst.aslist trav_dst.subst in
        let s = Subst.oflist (s1 @ s2) in

        let s =
          begin
            match (trav_src.term, trav_dst.term) with
            (* Subformula linking *)
            | `F f1, `F f2 ->
                f_unify goal.g_pregoal.g_env LEnv.empty s [ (f1, f2) ]
            (* Deep rewrite *)
            | `E e1, `E e2
              when let env = goal.g_pregoal.g_env in
                   let ty1 =
                     einfer (IPath.env proof src) (expr_of_term t_src)
                   in
                   let ty2 =
                     einfer (IPath.env proof dst) (expr_of_term t_dst)
                   in
                   Form.(t_equal env ty1 ty2) ->
                e_unify goal.g_pregoal.g_env LEnv.empty s [ (e1, e2) ]
            | _ -> None
          end
        in

        match s with
        | Some s when acyclic (Deps.subst deps s) ->
            let s1, s2 = List.split_at (List.length s1) (Subst.aslist s) in
            let s1 =
              s1
              |> rename trav_src.rename trav_dst.rename
              |> List.rev |> Subst.oflist
            in
            let s2 =
              s2
              |> rename trav_dst.rename trav_src.rename
              |> List.rev |> Subst.oflist
            in
            [ `Subform (s1, s2) ]
        | _ -> []
      with Invalid_argument _ -> []*)

  let opposite_pol_formulas : lpred =
   fun proof (src, dst) -> failwith "opposite_pol_formulas: todo"
  (*try
      let _, item_src, sub_src, _ = PathUtils.destr src proof in
      let _, item_dst, sub_dst, _ = PathUtils.destr dst proof in


      let src_pol =
        fst
        @@ Polarity.of_subterm
             (Polarity.of_item item_src, form_of_item item_src)
             sub_src
      in
      let dst_pol =
        fst
        @@ Polarity.of_subform
             (Polarity.of_item item_dst, form_of_item item_dst)
             sub_dst
      in
      match (src_pol, dst_pol) with
      | Neg, Pos | Pos, Neg | Sup, _ | _, Sup -> [ `Nothing ]
      | _ -> []
    with Invalid_argument _ | InvalidSubFormPath _ -> []*)

  let neg_eq_operand : lpred =
   fun proof (src, dst) -> failwith "neg_eq_operand: todo"
  (*let check (path : IPath.t) : bool =
      let _, item, (sub, term) = IPath.destr proof path in
      if sub = []
      then false
      else
        let eq_sub = List.remove_at (List.length sub - 1) sub in
        try
          match
            Polarity.of_subform
              (Polarity.of_item item, form_of_item item)
              eq_sub
          with
          | Neg, FPred ("_EQ", _) -> true
          | _ -> false
        with Invalid_argument _ | InvalidSubFormPath _ -> false
    in
    if check src || check dst then [ `Nothing ] else []*)

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
  let instantiate : hlpred = failwith "instantiate: todo"
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
