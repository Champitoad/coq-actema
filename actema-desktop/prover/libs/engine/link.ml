open CoreLogic
open Fo
open Utils

type link = IPath.t * IPath.t
type hyperlink = IPath.t list * IPath.t list

type linkaction =
  [ `Nothing
  | `Both of linkaction * linkaction
  | `Subform of Form.Subst.subst * Form.Subst.subst
  | `Instantiate of expr * IPath.t
  | `Rewrite of expr * expr * IPath.t list
  | `Fold of vname * IPath.t list
  | `Unfold of vname * IPath.t list ]

let hyperlink_of_link : link -> hyperlink = fun (src, dst) -> ([ src ], [ dst ])

(*******************************************************************************************)
(* Link predicates. *)

module Pred = struct
  type lpred = Proof.proof -> link -> linkaction list
  type hlpred = Proof.proof -> hyperlink -> linkaction list

  let lift : lpred -> hlpred = fun p pr -> function [ src ], [ dst ] -> p pr (src, dst) | _ -> []

  let mult : hlpred list -> hlpred =
    let aux : hlpred -> hlpred -> hlpred =
     fun p1 p2 pr lnk ->
      List.cartesian_product (p1 pr lnk) (p2 pr lnk) |> List.map (fun (a1, a2) -> `Both (a1, a2))
    in
    List.fold_left aux (fun _ _ -> [ `Nothing ])

  let add : hlpred list -> hlpred = fun ps pr lnk -> List.map (fun p -> p pr lnk) ps |> List.concat

  let if_empty : hlpred -> hlpred -> hlpred =
   fun p1 p2 pr lnk ->
    let actions = p1 pr lnk in
    if not (List.is_empty actions) then actions else p2 pr lnk

  let all_hyps_ipaths Proof.{ g_id; g_pregoal } =
    (* Get the list of hypotheses handles *)
    Proof.Hyps.ids g_pregoal.Proof.g_hyps
    |> (* Create a list of paths to each hypothesis *)
    List.map
      begin
        fun hd -> IPath.make (Handle.toint g_id) ~ctxt:{ kind = `Hyp; handle = Handle.toint hd }
      end

  let all_vars_ipaths ?(heads = true) Proof.{ g_id; g_pregoal } =
    let env = g_pregoal.Proof.g_env in
    (* Get the list of variable handles *)
    env.env_handles |> BiMap.codomain
    |> (* Create a list of paths to each variable's head and body *)
    List.concat_map
      begin
        fun hd ->
          (if heads
           then
             [ IPath.make (Handle.toint g_id) ~ctxt:{ kind = `Var `Head; handle = Handle.toint hd }
             ]
           else [])
          @
          match Vars.byid env hd with
          | Some (_, (_, Some _)) ->
              [ IPath.make (Handle.toint g_id) ~ctxt:{ kind = `Var `Body; handle = Handle.toint hd }
              ]
          | _ -> []
      end

  let all_items_ipaths ?heads goal =
    (IPath.to_concl goal :: all_hyps_ipaths goal) @ all_vars_ipaths ?heads goal

  (** [t_subs f] returns all the paths leading to a subterm in [t]. *)
  let t_subs (t : term) : int list list =
    let rec aux sub = function
      | `E (EFun (_, es)) | `F (FPred (_, es)) ->
          es
          |> List.mapi (fun i e ->
                 let sub = sub @ [ i ] in
                 sub :: aux sub (`E e))
          |> List.concat
      | `F (FConn (_, fs)) ->
          fs
          |> List.mapi (fun i f ->
                 let sub = sub @ [ i ] in
                 sub :: aux sub (`F f))
          |> List.concat
      | `F (FBind (_, _, _, f)) ->
          let sub = sub @ [ 0 ] in
          sub :: aux sub (`F f)
      | _ -> []
    in

    [] :: aux [] t

  (** [f_subs f] returns all the paths leading to a subformula in [f]. *)
  let f_subs (f : form) : int list list =
    let rec aux sub = function
      | FConn (_, fs) ->
          fs
          |> List.mapi (fun i f ->
                 let sub = sub @ [ i ] in
                 sub :: aux sub f)
          |> List.concat
      | FBind (_, _, _, f) ->
          let sub = sub @ [ 0 ] in
          sub :: aux sub f
      | _ -> []
    in

    [] :: aux [] f

  (** [e_subs f] returns all the paths leading to a subexpression in [f]. *)
  let e_subs (f : form) : int list list =
    let rec f_aux sub = function
      | FPred (_, es) ->
          es
          |> List.mapi (fun i e ->
                 let sub = sub @ [ i ] in
                 sub :: e_aux sub e)
          |> List.concat
      | FConn (_, fs) -> fs |> List.mapi (fun i f -> f_aux (sub @ [ i ]) f) |> List.concat
      | FBind (_, _, _, f) -> f_aux (sub @ [ 0 ]) f
      | _ -> []
    and e_aux sub = function
      | EVar _ -> []
      | EFun (_, es) ->
          es
          |> List.mapi (fun i e ->
                 let sub = sub @ [ i ] in
                 sub :: e_aux sub e)
          |> List.concat
    in

    f_aux [] f

  let remove_nothing =
    let rec doit = function
      | [] -> []
      | a :: l -> (
          match a with
          | `Nothing -> doit l
          | `Both (a, a') -> begin
              match doit [ a; a' ] with
              | [] -> doit l
              | [ a ] -> a :: doit l
              | [ a; a' ] -> `Both (a, a') :: doit l
              | _ -> assert false
            end
          | _ -> a :: doit l)
    in
    doit

  let string_of_linkaction proof =
    let rec doit = function
      | `Nothing -> "⊥"
      | `Both (a, a') -> Printf.sprintf "(%s, %s)" (doit a) (doit a')
      | `Subform _ -> "SubFormulaLinking"
      | `Instantiate _ -> "Instantiate"
      | `Rewrite (red, res, tgts) ->
          Printf.sprintf "%s[%s ~> %s]"
            (List.to_string ~sep:", " ~left:"{" ~right:"}"
               (fun p ->
                 let Proof.{ g_pregoal; _ }, _, (_, t) = IPath.destr proof p in
                 Notation.tostring g_pregoal.g_env t)
               tgts)
            red res
    in
    doit

  (** This module implements unification for subformula linking. *)
  module PreUnif = struct
    open Form

    module Deps = struct
      include Graph.Persistent.Digraph.Concrete (Name)

      let subst (deps : t) (s : Subst.subst) : t =
        (* For each item [x := e] in the substitution *)
        Subst.fold
          begin
            fun deps (x, tag) ->
              let fvs = match tag with Sbound e -> e_vars e | Sflex -> [] in
              (* For each variable [y] depending on [x] *)
              try
                fold_succ
                  begin
                    fun y deps ->
                      (* For each variable [z] occurring in [e] *)
                      List.fold_left
                        begin
                          fun deps (z, _) ->
                            (* Add an edge stating that [y] depends on [z] *)
                            add_edge deps z y
                        end
                        deps fvs
                  end
                  deps x deps
              with Invalid_argument _ -> deps
          end
          deps s
    end

    module TraverseDeps = Graph.Traverse.Dfs (Deps)

    let acyclic = not <<| TraverseDeps.has_cycle

    module Env = struct
      (** While traversing formulas in search for targets to unify, we need to
           record and update multiple informations handling the first-order content
           of the proof. We do so with a record of the form
            
             [{deps; rnm; subst}]
            
           where:

           - [deps] is a directed graph recording the dependency relation between
             existential and eigenvariables, in the same spirit of the dependency
             relation of expansion trees.
  
           - [rnm] is an association list, where each item [(z, x)] maps a fresh name
             [z] to the variable [x] it renames. Indeed, to avoid name clashes between
             bound variables of [f1] and [f2] during unification, we give them temporary
             fresh names, which are reverted to the original names with [rnm] when
             producing the final substitution for each formula.
            
           - [subst] is the substitution that will be fed to unification, in which we
             record existential variables in [Sflex] entries.
       *)
      type t = { deps : Deps.t; rnm : (name * name) list; subst : Subst.subst }
    end

    module State = Monad.State (Env)

    let traverse (p, t) i : (Polarity.t * term) State.t =
      let open State in
      match (p, t) with
      | Polarity.Pos, `F (FBind (`Forall, x, _, f)) 
      | Polarity.Neg, `F (FBind (`Exist, x, _, f)) ->
          get >>= fun { deps; rnm; subst } ->
          let z = EVars.fresh () in
          let exs = Subst.fold (fun acc (x, t) -> if t = Sflex then x :: acc else acc) [] subst in
          let deps = List.fold_left (fun deps y -> Deps.add_edge deps y z) deps exs in
          let rnm = (z, x) :: rnm in
          put { deps; rnm; subst } >>= fun _ ->
          let f = Form.Subst.f_apply1 (x, 0) (EVar (z, 0)) f in
          return (p, `F f)
      | Polarity.Neg, `F (FBind (`Forall, x, _, f)) 
      | Polarity.Pos, `F (FBind (`Exist, x, _, f)) ->
          get >>= fun ({ rnm; subst; _ } as st) ->
          let z = EVars.fresh () in
          let rnm = (z, x) :: rnm in
          let subst = Subst.push z Sflex subst in
          put { st with rnm; subst } >>= fun _ ->
          let f = Form.Subst.f_apply1 (x, 0) (EVar (z, 0)) f in
          return (p, `F f)
      | _ -> return (Polarity.of_direct_subterm (p, t) i)

    let traverse = State.fold traverse
  end

  let wf_subform ?(drewrite = false) : lpred =
    let open Form in
    let open PreUnif in
    let is_eq_operand proof (p : IPath.t) =
      try
        let eq_sub = List.(remove_at (length p.sub - 1) p.sub) in
        let eq_path = { p with sub = eq_sub } in
        let _, _, (_, t) = IPath.destr proof eq_path in
        match t with `F (FPred ("_EQ", _)) -> true | _ -> false
      with Invalid_argument _ -> false
    in

    fun proof (src, dst) ->
      let goal, item_src, (sub_src, t_src) = IPath.destr proof src in
      let _, item_dst, (sub_dst, t_dst) = IPath.destr proof dst in

      try
        let f1 = form_of_item item_src in
        let f2 = form_of_item item_dst in
        
        let p1 = Polarity.of_item item_src in
        let p2 = Polarity.of_item item_dst in

        let sub1 = sub_src in
        let sub2 = sub_dst in

        let deps, sp1, st1, rnm1, s1, sp2, st2, rnm2, s2 =
          let open State in
          run
            begin
              traverse (p1, `F f1) sub1 >>= fun (sp1, sf1) ->
              get >>= fun st1 ->
              put { st1 with rnm = []; subst = Subst.empty } >>= fun _ ->
              traverse (p2, `F f2) sub2 >>= fun (sp2, sf2) ->
              get >>= fun st2 ->
              return (st2.deps, sp1, sf1, st1.rnm, st1.subst, sp2, sf2, st2.rnm, st2.subst)
            end
            { deps = Deps.empty; rnm = []; subst = Subst.empty }
        in

        let s1 = Subst.aslist s1 in
        let s2 = Subst.aslist s2 in
        let s = Subst.oflist (s1 @ s2) in

        let s =
          begin
            match (st1, st2) with
            (* Subformula linking *)
            | `F f1, `F f2 when not drewrite -> begin
                (* Check that the two subformulas have opposite polarities. *)
                match (sp1, sp2) with
                | Pos, Neg | Neg, Pos | Sup, _ | _, Sup ->
                    (* Unify the two subformulas. *)
                    f_unify goal.g_pregoal.g_env LEnv.empty s [ (f1, f2) ]
                | _ -> None
              end
            (* Deep rewrite *)
            | `E e1, `E e2
              when drewrite
                   &&
                   let env = goal.g_pregoal.g_env in
                   let ty1 = einfer (IPath.env proof src) (expr_of_term t_src) in
                   let ty2 = einfer (IPath.env proof dst) (expr_of_term t_dst) in
                   Form.(t_equal env ty1 ty2) ->
                let eq1, eq2 = pair_map (is_eq_operand proof) (src, dst) in
                begin
                  match ((sp1, eq1), (sp2, eq2)) with
                  | (Neg, true), _ | _, (Neg, true) ->
                      e_unify goal.g_pregoal.g_env LEnv.empty s [ (e1, e2) ]
                  | _ -> None
                end
            | _ -> None
          end
        in

        match s with
        | Some s when acyclic (Deps.subst deps s) ->
            let s1, s2 = List.split_at (List.length s1) (Subst.aslist s) in

            let rename rnm1 rnm2 =
              List.map
                begin
                  fun (x, tag) ->
                    let get_name x rnm = Option.default x (List.assoc_opt x rnm) in
                    let x = get_name x rnm1 in
                    let tag =
                      let rec rename = function
                        | EVar (x, i) -> EVar (get_name x rnm2, i)
                        | EFun (f, es) -> EFun (f, List.map rename es)
                      in
                      match tag with Sbound e -> Sbound (rename e) | _ -> tag
                    in
                    (x, tag)
                end
            in

            let s1 = s1 |> rename rnm1 rnm2 |> List.rev |> Subst.oflist in
            let s2 = s2 |> rename rnm2 rnm1 |> List.rev |> Subst.oflist in

            [ `Subform (s1, s2) ]
        | _ -> []
      with Invalid_argument _ -> []

  let intuitionistic : lpred =
   fun proof (src, dst) ->
    let neg_count (p : IPath.t) =
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
      | m, n when (m > 0 && n > 0) || (m = 0 && n <= 1) || (m <= 1 && n = 0) -> [ `Nothing ]
      | _ -> []
    with InvalidSubFormPath _ | Invalid_argument _ -> []

  let instantiate : hlpred =
    let is_free_expr (t : term) (sub : int list) : bool =
      let lenv, subt =
        List.fold_left
          (fun (lenv, t) i ->
            let lenv =
              match t with `F (FBind (_, x, ty, _)) -> LEnv.enter lenv x ty | _ -> lenv
            in
            let t = direct_subterm t i in
            (lenv, t))
          (LEnv.empty, t) sub
      in
      match subt with `F _ -> false | `E e -> List.for_all (not <<| LEnv.exists lenv) (e_vars e)
    in

    fun proof (srcs, dsts) ->
      (* Link to quantified subformula *)
      let to_form p_wit p_form =
        let Proof.{ g_pregoal = goal; _ }, item_wit, (sub_wit, wit) = IPath.destr proof p_wit in

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
          | (Neg, `F (FBind (`Forall, _, ty, _)) | Pos, `F (FBind (`Exist, _, ty, _)))
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
      | _ -> []

  let rewrite : hlpred =
   fun proof lnk ->
    let rewrite_data (p : IPath.t) =
      if p.ctxt.kind = `Hyp
      then
        let _, it, _ = IPath.destr proof p in
        match (p.sub, form_of_item it) with
        | [ 0 ], FPred ("_EQ", [ red; res ]) | [ 1 ], FPred ("_EQ", [ res; red ]) -> Some (red, res)
        | _ -> None
      else None
    in

    try
      match (lnk, pair_map (List.hd |>> rewrite_data) lnk) with
      (* If it is a simple link where both ends are sides of equalities,
         disambiguate by rewriting into the destination *)
      | ([ _ ], [ dst ]), (Some (red, res), Some _) -> [ `Rewrite (red, res, [ dst ]) ]
      | ([ _ ], tgts), (Some (red, res), _) | (tgts, [ _ ]), (_, Some (red, res)) ->
          if List.exists (fun p -> p.IPath.ctxt.kind = `Var `Head) tgts
          then []
          else [ `Rewrite (red, res, tgts) ]
      | _ -> []
      (* Empty link end *)
    with Failure _ -> []

  let fold : hlpred =
   fun proof lnk ->
    let fold_data (p : IPath.t) =
      let _, it, _ = IPath.destr proof p in
      match (it, p.ctxt.kind, p.sub) with
      | `V (x, (_, Some _)), `Var where, [] -> Some (x, where)
      | _ -> None
    in

    try
      match (lnk, pair_map (List.hd |>> fold_data) lnk) with
      (* If it is a simple link where both ends are variable bodies,
         disambiguate by folding in the destination *)
      | ([ _ ], [ dst ]), (Some (x, `Body), Some (_, `Body)) -> [ `Fold (x, [ dst ]) ]
      | ([ p ], tgts), (Some (x, where), _) | (tgts, [ p ]), (_, Some (x, where)) ->
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
    with Failure _ -> []

  let search_linkactions ?(fixed_srcs : IPath.t list option) ?(fixed_dsts : IPath.t list option)
      (hlp : hlpred) proof ((src, dst) : link) : (hyperlink * linkaction list) list =
    let subpath p sub = IPath.{ root = p.root; ctxt = p.ctxt; sub = p.sub @ sub } in

    let query_actions lnk =
      match hlp proof lnk with _ :: _ as actions -> [ (lnk, actions) ] | [] -> []
    in

    let open Monad.List in
    match (fixed_srcs, fixed_dsts) with
    | Some srcs, Some dsts -> query_actions (srcs, dsts)
    | Some srcs, None ->
        let _, _, (_, t_dst) = IPath.destr proof dst in
        t_subs t_dst >>= fun sub_dst -> query_actions (srcs, [ subpath dst sub_dst ])
    | None, Some dsts ->
        let _, _, (_, t_src) = IPath.destr proof src in
        t_subs t_src >>= fun sub_src -> query_actions ([ subpath src sub_src ], dsts)
    | None, None ->
        let _, _, (_, t_src) = IPath.destr proof src in
        let _, _, (_, t_dst) = IPath.destr proof dst in
        t_subs t_src >>= fun sub_src ->
        t_subs t_dst >>= fun sub_dst ->
        query_actions ([ subpath src sub_src ], [ subpath dst sub_dst ])
end

type asource = { kind : asource_kind; selection : selection }
and asource_kind = [ `Click of IPath.t | `DnD of adnd | `Ctxt ]
and adnd = { source : IPath.t; destination : IPath.t option }
and selection = IPath.t list

type osource = [ `Click of IPath.t | `DnD of link | `Ctxt ]

type action_type =
  [ `Intro of int
  | `Elim of Handle.t * int
  | `Lemma of name
  | `Ind of Handle.t
  | `Simpl of IPath.t
  | `Red of IPath.t
  | `Indt of IPath.t
  | `Case of IPath.t
  | `Pbp of IPath.t
  | `Fold of vname
  | `Unfold of vname
  | `Hyperlink of hyperlink * linkaction list ]

type action = Handle.t * action_type

type aoutput =
  { description : string
  ; icon : string option
  ; highlights : IPath.t list
  ; kind : osource
  ; action : action
  }

(** [dnd_actions (dnd, selection)] computes all possible proof actions
      associated with the DnD action [dnd], and packages them as an array of
      output actions as specified in the JS API.

      More specifically, it will try to query actions for hyperlinks whose
      sources (resp. destinations) are those of [selection] occuring in
      [dnd.source] (resp. elsewhere), and which yield at least one action.

      If the source (resp. destination) selection is empty, it will search for
      hyperlinks with only one source (resp. destination) which is a subterm of
      [dnd.source] (resp. [dnd.destination]). If [dnd.destination] is [None], it
      will search for destinations everywhere in the current goal.
 *)
let dnd_actions ((dnd, selection) : adnd * selection) (proof : Proof.proof) : aoutput list =
  let (Proof.{ g_id; _ } as goal) = IPath.goal proof dnd.source in

  let srcsel : selection = List.filter (IPath.subpath dnd.source) selection in

  let dstsel : selection =
    List.remove_if (fun p -> p.IPath.ctxt.handle = dnd.source.ctxt.handle) selection
  in

  let hlpred_only_sel (p : Pred.hlpred) : Pred.hlpred =
   fun pr lnk -> if lnk = (srcsel, dstsel) then p pr lnk else []
  in

  let hlp =
    Pred.add
      [ Pred.mult (List.map Pred.lift [ Pred.wf_subform; Pred.intuitionistic ])
      ; Pred.if_empty (Pred.wf_subform ~drewrite:true |> Pred.lift) (Pred.rewrite |> hlpred_only_sel)
      ; Pred.fold |> hlpred_only_sel
      ; Pred.instantiate
      ]
  in

  let srcs, fixed_srcs =
    begin
      match srcsel with
      | [] -> ([ dnd.source ], None)
      | srcs -> ([ IPath.make (Handle.toint g_id) ], Some srcs)
    end
  in

  let dsts, fixed_dsts =
    begin
      match dstsel with
      | [] ->
          let dsts =
            begin
              match dnd.destination with
              | None ->
                  let src = dnd.source in
                  List.remove (Pred.all_items_ipaths goal) src
              | Some dst -> [ dst ]
            end
          in
          (dsts, None)
      | dsts -> ([ IPath.make (Handle.toint g_id) ], Some dsts)
    end
  in

  let open Monad.List in
  srcs >>= fun src ->
  dsts >>= fun dst ->
  let linkactions = Pred.search_linkactions hlp proof ?fixed_srcs ?fixed_dsts (src, dst) in

  linkactions >>= fun (((srcs, dsts) as lnk), actions) ->
  let actions = Pred.remove_nothing actions in
  srcs >>= fun src ->
  dsts >>= fun dst ->
  return
    { description = "Hyperlink"
    ; icon = None
    ; highlights = srcs @ dsts
    ; kind = `DnD (src, dst)
    ; action = (g_id, `Hyperlink (lnk, actions))
    }

type selpred = Proof.proof -> selection -> aoutput list

let selpred_add : selpred list -> selpred =
 fun ps pr sel -> List.map (fun p -> p pr sel) ps |> List.concat

let single_subterm_sel : selpred =
 fun proof sel ->
  let induction tgt =
    { description = "Induction"
    ; icon = Some "arrow-up-right-dots"
    ; highlights = sel
    ; kind = `Ctxt
    ; action = (IPath.gid proof tgt, `Indt tgt)
    }
  in

  let case_eq tgt =
    { description = "Case"
    ; icon = Some "list"
    ; highlights = sel
    ; kind = `Ctxt
    ; action = (IPath.gid proof tgt, `Case tgt)
    }
  in

  let pbp tgt =
    { description = "Point"
    ; icon = Some "hand-pointer"
    ; highlights = sel
    ; kind = `Ctxt
    ; action = (IPath.gid proof tgt, `Pbp tgt)
    }
  in

  match sel with
  | [ tgt ] -> begin
      match tgt.ctxt.kind with
      | `Var `Head -> [ induction tgt; case_eq tgt ]
      | _ ->
          [ { description = "Simplify"
            ; icon = Some "wand-magic-sparkles"
            ; highlights = sel
            ; kind = `Ctxt
            ; action = (IPath.gid proof tgt, `Simpl tgt)
            }
          ; { description = "Unfold"
            ; icon = Some "magnifying-glass"
            ; highlights = sel
            ; kind = `Ctxt
            ; action = (IPath.gid proof tgt, `Red tgt)
            }
          ; induction tgt
          ; case_eq tgt
          ; pbp tgt
          ]
    end
  | _ -> []

let rebuild_path i =
  let rec aux l = function 0 -> 0 :: l | i -> aux (1 :: l) (i - 1) in
  List.rev (aux [] i)

let rebuild_pathd l i =
  if i + 1 = l
  then [ 1 ]
  else
    let rec aux = function 0 -> [] | i -> 0 :: aux (i - 1) in
    if i = 0 then aux (l - 1) else aux (l - i - 1) @ [ 1 ]

let ctxt_actions (sel : selection) (proof : Proof.proof) : aoutput list =
  let selpred = selpred_add [ single_subterm_sel ] in
  selpred proof sel

let actions (proof : Proof.proof) (p : asource) : aoutput list =
  match p.kind with
  | `Click path -> begin
      let Proof.{ g_id = hd; g_pregoal = goal }, item, (_, _) = IPath.destr proof path in
      match item with
      | `C _ -> begin
          let iv = Proof.Tactics.ivariants proof ~goal_id:hd in
          let bv = List.length iv <= 1 in
          List.mapi
            (fun i x ->
              let hg =
                IPath.make (Handle.toint hd)
                  ~sub:(if bv then [] else rebuild_pathd (List.length iv) i)
              in
              { description = x
              ; icon = None
              ; highlights = [ hg ]
              ; kind = `Click hg
              ; action = (hd, `Intro i)
              })
            iv
        end
      | `H (rp, _) ->
          let ev = Proof.Tactics.evariants proof ~goal_id:hd ~hyp_id:rp in
          let bv = List.length ev <= 1 in
          List.mapi
            (fun i x ->
              let hg =
                IPath.make (Handle.toint hd)
                  ~ctxt:{ kind = `Hyp; handle = Handle.toint rp }
                  ~sub:(if bv then [] else rebuild_pathd (List.length ev) i)
              in
              { description = x
              ; icon = None
              ; highlights = [ hg ]
              ; kind = `Click hg
              ; action = (hd, `Elim (rp, i))
              })
            ev
      | `V (x, (ty, None)) when Form.t_equal goal.g_env ty Env.nat ->
          let rp = Vars.getid goal.g_env x |> Option.get in
          let hg =
            IPath.make (Handle.toint hd) ~ctxt:{ kind = `Var `Head; handle = Handle.toint rp }
          in
          [ { description = "Induction"
            ; icon = None
            ; highlights = [ hg ]
            ; kind = `Click hg
            ; action = (hd, `Ind hd)
            }
          ]
      | `V (x, (_, Some _)) ->
          let rp = Vars.getid goal.g_env x |> Option.get in

          let hg_unfold =
            IPath.make (Handle.toint hd) ~ctxt:{ kind = `Var `Head; handle = Handle.toint rp }
          in
          let hg_fold =
            IPath.make (Handle.toint hd) ~ctxt:{ kind = `Var `Body; handle = Handle.toint rp }
          in

          [ { description = "Unfold"
            ; icon = None
            ; highlights = [ hg_unfold ]
            ; kind = `Click hg_unfold
            ; action = (hd, `Unfold x)
            }
          ; { description = "Fold"
            ; icon = None
            ; highlights = [ hg_fold ]
            ; kind = `Click hg_fold
            ; action = (hd, `Fold x)
            }
          ]
      | _ -> []
    end
  | `DnD dnd -> dnd_actions (dnd, p.selection) proof
  | `Ctxt -> ctxt_actions p.selection proof
