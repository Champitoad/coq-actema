open Utils.Pervasive
open Api
open Logic
open Lang
open CoreLogic
open Link

type akind = Click of Path.t | DnD of Path.t * Path.t option | Ctxt
[@@deriving show]

type asource = { kind : akind; selection : Path.t list } [@@deriving show]

type preaction = Hyperlink of Link.hyperlink * Link.linkaction list
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

(** Create path to the root of every hypothesis (in a subgoal). *)
(*let all_hyps_ipaths Proof.{ g_id; g_pregoal } =
    (* Get the list of hypotheses handles *)
    Proof.Hyps.ids g_pregoal.Proof.g_hyps
    |> (* Create a list of paths to each hypothesis *)
    List.map
      begin
        fun hd ->
          IPath.make (Handle.toint g_id)
            ~ctxt:{ kind = `Hyp; handle = Handle.toint hd }
      end

  (** Create a path to the body (and optionally the head) of every variable (in a subgoal). *)
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
             [ IPath.make (Handle.toint g_id)
                 ~ctxt:{ kind = `Var `Head; handle = Handle.toint hd }
             ]
           else [])
          @
          match Vars.byid env hd with
          | Some (_, (_, Some _)) ->
              [ IPath.make (Handle.toint g_id)
                  ~ctxt:{ kind = `Var `Body; handle = Handle.toint hd }
              ]
          | _ -> []
      end

  (** Create a path to the following items in a subgoal :
      - the root of the goal.
      - the root of every hypothesis.
      - the body (and optionally the head) of every variable. *)
  let all_items_ipaths ?heads goal =
    (IPath.to_concl goal :: all_hyps_ipaths goal) @ all_vars_ipaths ?heads goal*)

(* TODO : check this works when [path] points to a variable. *)
let all_subpaths proof path : Path.t list =
  let term = PathUtils.term path proof in
  let subs = TermUtils.all_subs term in
  List.map (fun sub -> Path.{ goal = path.goal; kind = path.kind; sub }) subs

(* TODO : add variables in here. *)
let all_goal_subpaths proof goal : Path.t list =
  let roots =
    Path.make ~kind:Concl goal.g_id
    :: List.map
         (fun name -> Path.make ~kind:(Hyp name) goal.g_id)
         (Hyps.ids goal.g_pregoal.g_hyps)
  in
  List.concat_map (all_subpaths proof) roots

(** [dnd_actions src dst selection proof] computes all possible proof actions
    associated with the DnD action [DnD (src, dst)].

    To see more specifically what hyperlinks are tested,
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
      [ Pred.wf_subform
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
    | _ -> []

  let rebuild_path i =
    let rec aux l = function 0 -> 0 :: l | i -> aux (1 :: l) (i - 1) in
    List.rev (aux [] i)

  let rebuild_pathd l i =
    if i + 1 = l
    then [ 1 ]
    else
      let rec aux = function 0 -> [] | i -> 0 :: aux (i - 1) in
      if i = 0 then aux (l - 1) else aux (l - i - 1) @ [ 1 ]*)

let ctxt_actions (sel : Path.t list) (proof : Proof.t) : aoutput list = []
(*let selpred = selpred_add [ single_subterm_sel ] in
  selpred proof sel*)

let click_actions (selection : Path.t list) (proof : Proof.t) : aoutput list =
  []
(*begin
    let Proof.{ g_id = hd; g_pregoal = goal }, item, (_, _) =
      IPath.destr proof path
    in
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
            ; goal_handle = hd
            ; action = `Intro i
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
            ; goal_handle = hd
            ; action = `Elim (rp, i)
            })
          ev
    | `V (x, (ty, None)) when Form.t_equal goal.g_env ty Env.nat ->
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
    | `V (x, (_, Some _)) ->
        let rp = Vars.getid goal.g_env x |> Option.get in

        let hg_unfold =
          IPath.make (Handle.toint hd)
            ~ctxt:{ kind = `Var `Head; handle = Handle.toint rp }
        in
        let hg_fold =
          IPath.make (Handle.toint hd)
            ~ctxt:{ kind = `Var `Body; handle = Handle.toint rp }
        in

        [ { description = "Unfold"
          ; icon = None
          ; highlights = [ hg_unfold ]
          ; kind = `Click hg_unfold
          ; goal_handle = hd
          ; action = `Unfold x
          }
        ; { description = "Fold"
          ; icon = None
          ; highlights = [ hg_fold ]
          ; kind = `Click hg_fold
          ; goal_handle = hd
          ; action = `Fold x
          }
        ]
    | _ -> []
  end*)

let actions (proof : Proof.t) (source : asource) : aoutput list =
  match source.kind with
  | Click path -> click_actions source.selection proof
  | DnD (src, dst) -> dnd_actions src dst source.selection proof
  | Ctxt -> ctxt_actions source.selection proof
