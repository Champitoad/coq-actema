open Utils.Pervasive
open Api
open Logic
open Lang
open ProverLogic
open Link

type akind = Click of Path.t | DnD of Path.t * Path.t option | Ctxt
[@@deriving show]

type asource = { kind : akind; selection : Path.t list } [@@deriving show]

type preaction =
  | Exact of Name.t
  | Intro of int
  | Elim of Name.t * int
  | Simpl of Path.t
  | Case of Term.t
  | CaseIntro of int
  | Ind of Term.t
  | IndIntro of int
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

(********************************************************************************)
(** Drag and drop actions. *)
(********************************************************************************)

(** [is_nat_constant t] checks if [t] is a natural number of the form [S (S (... O))]. *)
let rec is_nat_constant (t : Term.t) : bool =
  match t with
  | Cst c when c = Constants.zero -> true
  | App (_, f, [ arg ]) when f = Term.mkCst Constants.succ ->
      is_nat_constant arg
  | _ -> false

let rec displayed_subs_rec env (term : Term.t) sub acc : int list list =
  match term with
  | FVar _ | BVar _ | Cst _ | Sort _ -> sub :: acc
  | Lambda (_, x, ty, body) | Prod (_, x, ty, body) ->
      let acc = displayed_subs_rec env ty (0 :: sub) acc in
      let acc = displayed_subs_rec env body (1 :: sub) acc in
      sub :: acc
  | _ when is_nat_constant term -> sub :: acc
  | App (_, f, args) ->
      let elts =
        match f with
        | Cst name ->
            let info =
              match Name.Map.find_opt name env.Env.pp_info with
              | Some info -> info
              | None -> Env.default_pp_info (Name.show name)
            in
            (0, f) :: Env.filter_args info (indices ~start:1 args)
        | _ -> indices (f :: args)
      in
      sub
      :: List.fold_left
           (fun acc (i, x) -> displayed_subs_rec env x (i :: sub) acc)
           acc elts

(** [displayed_subs t] returns the list of all paths [sub] that 
    points to a subterm of [t] that is actually displayed to the user.
    For instance it doesn't return paths inside natural number constant,
    or paths to implicit arguments in applications. *)
let displayed_subs env t = displayed_subs_rec env t [] [] |> List.map List.rev

(* TODO : check this works when [path] points to a variable. *)
let all_subpaths proof path : Path.t list =
  let goal, _, _, term = PathUtils.destr path proof in
  let subs = displayed_subs goal.g_pregoal.g_env term in
  List.map
    (fun sub ->
      Path.{ goal = path.goal; kind = path.kind; sub = path.sub @ sub })
    subs

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
  let dst_sel = List.filter (not <<< Path.same_item input_src) selection in

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
        |> List.filter (not <<< Path.same_item input_src)
        |> List.(map singleton)
    | dst_sel, _ ->
        (* When the destination selection is non-empty,
           we use dst_sel as a single hyperlink destination. *)
        [ dst_sel ]
  in

  (*Js_log.log "**********************************************************";
    Js_log.log
    @@ Format.sprintf "Sources : \n%s\nDests : \n%s\n"
         (List.to_string (List.to_string Path.to_string) hyperlink_sources)
         (List.to_string (List.to_string Path.to_string) hyperlink_dests);*)

  (* The hyperlink predicate we use for DnD actions. *)
  (*let hlpred_only_sel (pred : Pred.hlpred) : Pred.hlpred =
     fun proof link -> if link = (src_sel, dst_sel) then pred proof link else []
    in*)
  let hlpred =
    Pred.add
      [ Pred.wf_subform
      ; Pred.deep_rewrite
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
  (* Make sure there is at least one linkaction. *)
  let* _ = guard (linkactions <> []) in
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

(********************************************************************************)
(** Contextual actions. *)
(********************************************************************************)

let is_hyp (path : Path.t) : bool =
  match path.kind with Hyp _ -> true | _ -> false

let is_concl (path : Path.t) : bool =
  match path.kind with Concl -> true | _ -> false

let is_var (path : Path.t) : bool =
  match path.kind with VarHead _ | VarType _ | VarBody _ -> true | _ -> false

let is_var_head (path : Path.t) : bool =
  match path.kind with VarHead _ -> true | _ -> false

(** [Simpl] action. *)
let simplify_actions (selection : Path.t list) proof : aoutput list =
  match selection with
  | [ sel ] when is_hyp sel || is_concl sel -> begin
      [ { description = "Simplify"
        ; icon = Some "wand-magic-sparkles"
        ; highlights = [ sel ]
        ; kind = Ctxt
        ; goal_id = sel.goal
        ; preaction = Simpl sel
        }
      ]
    end
  | _ -> []

(** Some heurisistics to decide if we disallow case analysis/induction 
    on a term. If this returns [true], then case analysis is forbidden. *)
let forbid_case_analysis env context subterm : bool =
  match (subterm : Term.t) with
  | Sort _ | Lambda _ | Prod _ -> true
  | _ -> begin
      let subterm_ty = TermUtils.typeof env context subterm in
      match subterm_ty with Prod _ -> true | _ -> false
    end

(** [Case] and [Ind] action. *)
let case_ind_actions (selection : Path.t list) proof : aoutput list =
  match selection with
  (* This works for any selection path, even when it points to the head of a variable. *)
  | [ sel ] ->
      (* Check the selected subterm contains no free variables. *)
      let goal = Proof.byid proof sel.goal in
      let context, sel_subterm =
        TermUtils.subterm (PathUtils.term sel proof) sel.sub
      in
      if Term.contains_fvars sel_subterm
         || forbid_case_analysis goal.g_env context sel_subterm
      then []
      else
        (* We passed the tests : the action is (probably) valid. *)
        [ { description = "Case"
          ; icon = Some "list"
          ; highlights = [ sel ]
          ; kind = Ctxt
          ; goal_id = sel.goal
          ; preaction = Case sel_subterm
          }
        ; { description = "Induction"
          ; icon = Some "arrow-up-right-dots"
          ; highlights = [ sel ]
          ; kind = Ctxt
          ; goal_id = sel.goal
          ; preaction = Ind sel_subterm
          }
        ]
  | _ -> []

(** Helper function for [case_ind_intro_actions]. 
    Returns [n] the number of products traversed, and [ctx] and [term]
    the subterm we perform case analysis on. *)
let rec traverse_products n ctx (term : Term.t) sub :
    (int * Context.t * Term.t) option =
  match (sub, term) with
  (* Base case : we point to a forall. *)
  | [], Prod (_, x, ty, body) when Term.contains_loose_bvars body ->
      let fvar, ctx = Context.add_fresh x ty ctx in
      Some (n + 1, ctx, Term.mkFVar fvar)
  (* Base case : we point to the left of an implication. *)
  | [ 0 ], Prod (_, x, ty, body) when not @@ Term.contains_loose_bvars body ->
      Some (n + 1, ctx, ty)
  (* Go to the right of a forall or an implication. *)
  | 1 :: sub, Prod (_, x, ty, body) ->
      let fvar, ctx = Context.add_fresh x ty ctx in
      traverse_products (n + 1) ctx (Term.instantiate fvar body) sub
  (* Invalid cases. *)
  | _ -> None

(** [CaseIntro] and [IndIntro] action. *)
let case_ind_intro_actions (selection : Path.t list) proof : aoutput list =
  match selection with
  | [ sel ] when is_concl sel ->
      let goal = Proof.byid proof sel.goal in
      let sel_term = PathUtils.term sel proof in
      (* Count how many products we have to traverse to get to the selected subterm. *)
      begin
        match traverse_products 0 Context.empty sel_term sel.sub with
        | Some (n, ctx, subterm)
          when not @@ forbid_case_analysis goal.g_env ctx subterm ->
            (* We passed the tests : the action is (probably) valid. *)
            [ { description = "Case"
              ; icon = Some "list"
              ; highlights = [ sel ]
              ; kind = Ctxt
              ; goal_id = sel.goal
              ; preaction = CaseIntro n
              }
            ; { description = "Induction"
              ; icon = Some "arrow-up-right-dots"
              ; highlights = [ sel ]
              ; kind = Ctxt
              ; goal_id = sel.goal
              ; preaction = IndIntro n
              }
            ]
        | _ -> []
      end
  | _ -> []

let ctxt_actions (selection : Path.t list) (proof : Proof.t) : aoutput list =
  simplify_actions selection proof
  @ case_ind_actions selection proof
  @ case_ind_intro_actions selection proof

(*let induction tgt =
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
  in*)
(*match selection with
  | [ sel ] -> begin
      match sel.kind with
      | VarHead v -> [ (*induction tgt; case_eq tgt*) ]
      | _ ->
            (*; { description = "Unfold"
                ; icon = Some "magnifying-glass"
                ; highlights = sel
                ; kind = `Ctxt
                ; goal_handle = IPath.gid proof tgt
                ; action = `Red tgt
                }
              ; induction tgt
              ; case_eq tgt
              ; pbp tgt*)

    end
  | _ -> []*)

(********************************************************************************)
(** Click actions. *)
(********************************************************************************)

(** Get all the introduction variants of a given goal.
    This returns a list of [description, sub] where [sub] is the subpath
    in the conclusion which should be highlighted. *)
let intro_variants goal : (string * int list) list =
  match goal.g_concl with
  | App (_, Cst eq, [ _; _; _ ]) when Name.equal eq Constants.eq ->
      [ ("reflexivity", []) ]
  | App (_, Cst and_, [ _; _ ]) when Name.equal and_ Constants.and_ ->
      [ ("split", []) ]
  | App (_, Cst or_, [ _; _ ]) when Name.equal or_ Constants.or_ ->
      [ ("left", [ 1 ]); ("right", [ 2 ]) ]
  | App (_, Cst equiv_, [ _; _ ]) when Name.equal equiv_ Constants.equiv ->
      [ ("split", []) ]
  | App (_, Cst not_, [ _ ]) when Name.equal not_ Constants.not ->
      [ ("intro", []) ]
  | Cst true_ when true_ = Constants.true_ -> [ ("constructor", []) ]
  | Prod _ | Lambda _ -> [ ("intro", []) ]
  | _ -> []

let is_cst : Term.t -> bool = function Term.Cst _ -> true | _ -> false

(** Get all the elimination variants of a given hypothesis. 
    This returns a list of [description, sub] where [sub] is the subpath
    in the hypothesis which should be highlighted. *)
let elim_variants hyp : (string * int list) list =
  match hyp.h_form with
  | App (_, Cst eq, [ _; t1; t2 ]) when Name.equal eq Constants.eq ->
      [ ("rewrite->", [ 2 ]); ("rewrite<-", [ 3 ]) ]
  | App (_, Cst equiv, [ _; _ ]) when Name.equal equiv Constants.equiv ->
      [ ("destruct", []) ]
  | App (_, Cst and_, [ _; _ ]) when Name.equal and_ Constants.and_ ->
      [ ("destruct", []) ]
  | App (_, Cst or_, [ _; _ ]) when Name.equal or_ Constants.or_ ->
      [ ("destruct", []) ]
  | App (_, Cst not, [ _ ]) when Name.equal not Constants.not ->
      [ ("apply", []) ]
  | App (_, Cst ex, [ _; Lambda _ ]) when Name.equal ex Constants.ex ->
      [ ("destruct", []) ]
  | Cst true_ when Name.equal true_ Constants.true_ -> [ ("destruct", []) ]
  | Cst false_ when Name.equal false_ Constants.false_ -> [ ("destruct", []) ]
  | Prod (_, x, ty, body) when not @@ Term.contains_loose_bvars body ->
      [ ("apply", []) ]
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
        if Term.alpha_equiv hyp.h_form goal.g_pregoal.g_concl
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

(********************************************************************************)
(** Putting it all together. *)
(********************************************************************************)

let actions (proof : Proof.t) (source : asource) : aoutput list =
  match source.kind with
  | Click path -> click_actions path source.selection proof
  | DnD (src, dst) -> dnd_actions src dst source.selection proof
  | Ctxt -> ctxt_actions source.selection proof
