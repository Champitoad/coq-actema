open Utils.Pervasive
open Api
open Logic
open Lang
open CoreLogic
open Link

type akind = Click of Path.t | DnD of Path.t * Path.t option | Ctxt
[@@deriving show]

type asource = { kind : akind; selection : Path.t list } [@@deriving show]

type preaction =
  | Exact of Name.t
  | Intro of int
  | Elim of Name.t * int
  | Fold of Name.t
  | Unfold of Name.t
  | Hyperlink of Link.hyperlink * Link.linkaction list
[@@deriving show]

type aoutput =
  { description : string
  ; icon : string option
  ; highlights : Path.t list
  ; kind : akind
  ; goal_id : int
  ; preaction : preaction
  }
[@@deriving show]

(* TODO : check this works when [path] points to a variable. *)
let all_subpaths proof path : Path.t list =
  let term = PathUtils.term path proof in
  let subs = TermUtils.all_subs term in
  List.map (fun sub -> Path.{ goal = path.goal; kind = path.kind; sub }) subs

(* TODO : handle variables. *)
let all_goal_subpaths proof goal : Path.t list =
  let roots =
    Path.make ~kind:Concl goal.g_id
    :: List.map
         (fun name -> Path.make ~kind:(Hyp name) goal.g_id)
         (Hyps.names goal.g_pregoal.g_hyps)
  in
  List.concat_map (all_subpaths proof) roots

(** [dnd_actions src dst selection proof] computes all possible link action actions
    associated with the DnD action [DnD (src, dst)].

    To see more specifically which hyperlinks are tested,
    look at the definition of [hyperlink_sources] and [hyperlink_dests] below. *)
let dnd_actions (input_src : Path.t) (input_dst : Path.t option)
    (selection : Path.t list) (proof : Proof.t) : aoutput list =
  let goal = PathUtils.goal input_src proof in

  (* Compute the source selection, i.e. all subterms of [src] that are selected. *)
  let src_sel = List.filter (Path.is_prefix input_src) selection in

  (* Compute the destination selection, i.e. all terms that
     are selected but in a different item from [src]. *)
  let dst_sel = List.remove_if (Path.same_item input_src) selection in

  (* Compute the hyperlink sources. *)
  let hyperlink_sources =
    match src_sel with
    | [] ->
        (* When the source selection is empty,
           we use all subterms of input_src as hyperlink sources. *)
        all_subpaths proof input_src |> List.(map singleton)
    | _ ->
        (* When the source selection is non-empty,
           we use src_sel as a single hyperlink source. *)
        [ src_sel ]
  in

  (* Compute the hyperlink destinations. *)
  let hyperlink_dests =
    match (dst_sel, input_dst) with
    | [], Some input_dst ->
        (* When the destination selection is empty and the destination path exists,
           we use all subterms of input_dst as hyperlink destinations. *)
        all_subpaths proof input_dst |> List.(map singleton)
    | [], None ->
        (* When the destination selection is empty and the destination path does not exist,
           we use all subpaths of all items, except the source item. *)
        all_goal_subpaths proof goal
        |> List.remove_if (Path.same_item input_src)
        |> List.(map singleton)
    | dst_sel, _ ->
        (* When the destination selection is non-empty,
           we use dst_sel as a single hyperlink destination. *)
        [ dst_sel ]
  in

  (* The hyperlink predicate we use for DnD actions. *)
  (*let hlpred_only_sel (pred : Pred.hlpred) : Pred.hlpred =
     fun proof link -> if link = (src_sel, dst_sel) then pred proof link else []
    in*)
  let hlpred =
    Pred.add
      [ Pred.lift Pred.unifiable
        (*; Pred.if_empty Pred.deep_rewrite (Pred.rewrite |> hlpred_only_sel)
          ; Pred.fold |> hlpred_only_sel
          ; Pred.instantiate*)
      ]
  in

  (* Evaluate the hyperlink predicate on every hyperlink. *)
  let open Utils.Monad.List in
  let* hyper_src = hyperlink_sources in
  let* hyper_dst = hyperlink_dests in
  let linkactions =
    hlpred proof (hyper_src, hyper_dst) |> List.filter_map Link.remove_nothing
  in
  (* Build the action output. *)
  let* src = hyper_src in
  let* dst = hyper_dst in
  return
    { description = "Hyperlink"
    ; icon = None
    ; highlights = hyper_src @ hyper_dst
    ; kind = DnD (src, Some dst)
    ; goal_id = goal.g_id
    ; preaction = Hyperlink ((hyper_src, hyper_dst), linkactions)
    }

(*type selpred = Proof.proof -> selection -> aoutput list

  let selpred_add : selpred list -> selpred =
   fun ps pr sel -> List.map (fun p -> p pr sel) ps |> List.concat

  let single_subterm_sel : selpred =
   fun proof sel ->
    let induction tgt =
      { description = "Induction"
      ; icon = Some "arrow-up-right-dots"
      ; highlights = sel
      ; kind = `Ctxt
      ; goal_handle = IPath.gid proof tgt
      ; action = `Indt tgt
      }
    in

    let case_eq tgt =
      { description = "Case"
      ; icon = Some "list"
      ; highlights = sel
      ; kind = `Ctxt
      ; goal_handle = IPath.gid proof tgt
      ; action = `Case tgt
      }
    in

    let pbp tgt =
      { description = "Point"
      ; icon = Some "hand-pointer"
      ; highlights = sel
      ; kind = `Ctxt
      ; goal_handle = IPath.gid proof tgt
      ; action = `Pbp tgt
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
              ; goal_handle = IPath.gid proof tgt
              ; action = `Simpl tgt
              }
            ; { description = "Unfold"
              ; icon = Some "magnifying-glass"
              ; highlights = sel
              ; kind = `Ctxt
              ; goal_handle = IPath.gid proof tgt
              ; action = `Red tgt
              }
            ; induction tgt
            ; case_eq tgt
            ; pbp tgt
            ]
      end
    | _ -> []*)

(* This seems very hacky. *)
(*let rebuild_pathd l i =
  if i + 1 = l
  then [ 1 ]
  else
    let rec aux = function 0 -> [] | i -> 0 :: aux (i - 1) in
    if i = 0 then aux (l - 1) else aux (l - i - 1) @ [ 1 ]*)

let ctxt_actions (sel : Path.t list) (proof : Proof.t) : aoutput list = []
(*let selpred = selpred_add [ single_subterm_sel ] in
  selpred proof sel*)

(** Get all the introduction variants of a given goal.
    This returns a list of [description, sub] where [sub] is the subpath
    in the conclusion which should be highlighted. *)
let intro_variants goal : (string * int list) list =
  match goal.g_concl with
  | App (Cst name, _) ->
      if name = Name.eq
      then [ ("reflexivity", []) ]
      else if name = Name.and_
      then [ ("split", []) ]
      else if name = Name.or_
      then [ ("left", [ 1 ]); ("right", [ 2 ]) ]
      else if name = Name.equiv
      then [ ("split", []) ]
      else if name = Name.not
      then [ ("intro", []) ]
      else if name = Name.ex
      then [ ("exists", []) ]
      else []
  | Cst name when name = Name.true_ -> [ ("constructor", []) ]
  | Arrow _ | Prod _ | Lambda _ -> [ ("intro", []) ]
  | _ -> []

(** Get all the elimination variants of a given hypothesis. 
    This returns a list of [description, sub] where [sub] is the subpath
    in the hypothesis which should be highlighted. *)

let elim_variants hyp : (string * int list) list =
  match hyp.h_form with
  | App (Cst name, _) ->
      if name = Name.eq
      then [ ("rewrite ->", [ 2 ]); ("rewrite <-", [ 3 ]) ]
      else if name = Name.equiv
      then [ ("destruct", []) ]
      else if name = Name.or_
      then [ ("destruct", []) ]
      else if name = Name.not
      then [ ("destruct", []) ]
      else if name = Name.ex
      then [ ("destruct", []) ]
      else []
  | Cst name ->
      if name = Name.true_
      then [ ("destruct", []) ]
      else if name = Name.false_
      then [ ("destruct", []) ]
      else []
  | Arrow _ -> [ ("apply", []) ]
  | _ -> []

let click_actions (path : Path.t) (selection : Path.t list) (proof : Proof.t) :
    aoutput list =
  let goal, item, _, _ = PathUtils.destr path proof in
  match item with
  (* On the conclusion, we can apply an introduction rule. *)
  | Concl concl ->
      List.mapi
        begin
          fun i (description, sub) ->
            let path = Path.make goal.g_id ~sub in
            { description
            ; icon = None
            ; highlights = [ path ]
            ; kind = Click path
            ; goal_id = goal.g_id
            ; preaction = Intro i
            }
        end
        (intro_variants goal.g_pregoal)
  (* On a hypothesis, we can apply an elimination rule, or use the exact tactic. *)
  | Hyp (hyp_name, _) ->
      let hyp = Hyps.by_name goal.g_pregoal.g_hyps hyp_name in
      (* Elimination. *)
      let elim_actions =
        List.mapi
          (fun i (description, sub) ->
            let path = Path.make goal.g_id ~kind:(Hyp hyp_name) ~sub in
            { description
            ; icon = None
            ; highlights = [ path ]
            ; kind = Click path
            ; goal_id = goal.g_id
            ; preaction = Elim (hyp_name, i)
            })
          (elim_variants hyp)
      in
      (* Exact. *)
      let exact_actions =
        if TermUtils.alpha_equiv hyp.h_form goal.g_pregoal.g_concl
        then
          let path = Path.make goal.g_id ~kind:(Hyp hyp_name) in
          [ { description = "exact"
            ; icon = None
            ; highlights = [ path ]
            ; kind = Click path
            ; goal_id = goal.g_id
            ; preaction = Exact hyp_name
            }
          ]
        else []
      in
      (* Concatenate the results. *)
      elim_actions @ exact_actions
  (* On a variable with a body, we can fold/unfold. *)
  | Var (vname, _, Some _) ->
      (*let rp = Vars.getid goal.g_env x |> Option.get in*)
      let unfold_path = Path.make ~kind:(VarHead vname) goal.g_id in
      let fold_path = Path.make ~kind:(VarBody vname) goal.g_id in

      [ { description = "Unfold"
        ; icon = None
        ; highlights = [ unfold_path ]
        ; kind = Click unfold_path
        ; goal_id = goal.g_id
        ; preaction = Unfold vname
        }
      ; { description = "Fold"
        ; icon = None
        ; highlights = [ fold_path ]
        ; kind = Click fold_path
        ; goal_id = goal.g_id
        ; preaction = Fold vname
        }
      ]
  (*| `V (x, (ty, None)) when Form.t_equal goal.g_env ty Env.nat ->
        let rp = Vars.getid goal.g_env x |> Option.get in
        let hg =
          IPath.make (Handle.toint hd)
            ~ctxt:{ kind = `Var `Head; handle = Handle.toint rp }
        in
        [ { description = "Induction"
          ; icon = None
          ; highlights = [ hg ]
          ; kind = `Click hg
          ; goal_handle = hd
          ; action = `Ind rp
          }
        ]
  *)
  | _ -> []

let actions (proof : Proof.t) (source : asource) : aoutput list =
  match source.kind with
  | Click path -> click_actions path source.selection proof
  | DnD (src, dst) -> dnd_actions src dst source.selection proof
  | Ctxt -> ctxt_actions source.selection proof
