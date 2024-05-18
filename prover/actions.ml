(*open Fo
open CoreLogic
open Link
open Utils

type selection = IPath.t list [@@deriving show]
type adnd = { source : IPath.t; destination : IPath.t option } [@@deriving show]

type asource_kind = [ `Click of IPath.t | `DnD of adnd | `Ctxt ]
[@@deriving show]

type asource = { kind : asource_kind; selection : selection } [@@deriving show]

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
[@@deriving show]

type aoutput_kind = [ `Click of IPath.t | `DnD of Link.link | `Ctxt ]
[@@deriving show]

type aoutput =
  { description : string
  ; icon : string option
  ; highlights : IPath.t list
  ; kind : aoutput_kind
  ; goal_handle : Handle.t
  ; action : action_type
  }
[@@deriving show]

(** Create path to the root of every hypothesis (in a subgoal). *)
let all_hyps_ipaths Proof.{ g_id; g_pregoal } =
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
  (IPath.to_concl goal :: all_hyps_ipaths goal) @ all_vars_ipaths ?heads goal

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
let dnd_actions ((dnd, selection) : adnd * selection) (proof : Proof.proof) :
    aoutput list =
  let (Proof.{ g_id; _ } as goal) = IPath.goal proof dnd.source in

  let srcsel : selection = List.filter (IPath.subpath dnd.source) selection in

  let dstsel : selection =
    List.remove_if
      (fun p -> p.IPath.ctxt.handle = dnd.source.ctxt.handle)
      selection
  in

  let hlpred_only_sel (pred : Pred.hlpred) : Pred.hlpred =
   fun proof link -> if link = (srcsel, dstsel) then pred proof link else []
  in

  let hlp =
    Pred.add
      [ Pred.wf_subform
      ; Pred.if_empty Pred.deep_rewrite (Pred.rewrite |> hlpred_only_sel)
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
                  List.remove (all_items_ipaths goal) src
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
  let linkactions =
    Pred.search_linkactions hlp proof ?fixed_srcs ?fixed_dsts (src, dst)
  in

  linkactions >>= fun (((srcs, dsts) as lnk), actions) ->
  let actions = List.filter_map Link.remove_nothing actions in
  srcs >>= fun src ->
  dsts >>= fun dst ->
  return
    { description = "Hyperlink"
    ; icon = None
    ; highlights = srcs @ dsts
    ; kind = `DnD (src, dst)
    ; goal_handle = g_id
    ; action = `Hyperlink (lnk, actions)
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
    if i = 0 then aux (l - 1) else aux (l - i - 1) @ [ 1 ]

let ctxt_actions (sel : selection) (proof : Proof.proof) : aoutput list =
  let selpred = selpred_add [ single_subterm_sel ] in
  selpred proof sel

let actions (proof : Proof.proof) (p : asource) : aoutput list =
  match p.kind with
  | `Click path -> begin
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
    end
  | `DnD dnd -> dnd_actions (dnd, p.selection) proof
  | `Ctxt -> ctxt_actions p.selection proof
 *)
