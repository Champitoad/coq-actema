open Utils
open Fo
module Js = Js_of_ocaml.Js

exception InvalidGoalId of Handle.t
exception InvalidHyphId of Handle.t
exception SubgoalNotOpened of Handle.t


(** The type of a single hypothesis. *)
type hyp =
  { h_src : Handle.t option  (** A unique identifier for the hypothesis. *)
  ; h_gen : int
  ; h_form : form  (** The formula contained in the hypothesis. *)
  }

module Hyps : sig
  type t

  val empty : t
  val byid : t -> Handle.t -> hyp
  val add : t -> Handle.t -> hyp -> t
  val remove : t -> Handle.t -> t
  val move : t -> Handle.t -> Handle.t option -> t
  val bump : t -> t
  val ids : t -> Handle.t list
  val map : (hyp -> hyp) -> t -> t
  val iter : (hyp -> unit) -> t -> unit
  val to_list : t -> (Handle.t * hyp) list
  val of_list : (Handle.t * hyp) list -> t
end = struct
  (** A list of hypotheses, each with a handle. *)
  type t = (Handle.t * hyp) list

  let empty : t = []

  let byid (hyps : t) (id : Handle.t) =
    Option.get_exn (List.Exceptionless.assoc id hyps) (InvalidHyphId id)

  let add (hyps : t) (id : Handle.t) (h : hyp) : t =
    assert (Option.is_none (List.Exceptionless.assoc id hyps));
    (id, h) :: hyps

  let remove (hyps : t) (id : Handle.t) : t = List.filter (fun (x, _) -> not (Handle.eq x id)) hyps

  let move (hyps : t) (from : Handle.t) (before : Handle.t option) =
    let tg = byid hyps from in
    let hyps = remove hyps from in

    match before with
    | None -> (from, tg) :: hyps
    | Some before ->
        let pos, _ =
          Option.get_exn
            (List.Exceptionless.findi (fun _ (x, _) -> Handle.eq x before) hyps)
            (InvalidHyphId before)
        in
        let post, pre = List.split_at (1 + pos) hyps in
        post @ ((from, tg) :: pre)

  let bump (hyps : t) : t = List.map (fun (id, h) -> (id, { h with h_gen = h.h_gen + 1 })) hyps
  let ids (hyps : t) = List.fst hyps
  let map f (hyps : t) = List.map (snd_map f) hyps
  let iter f (hyps : t) = List.iter (fun (_handle, hyp) -> f hyp) hyps

  let diff (hs1 : t) (hs2 : t) =
    hs1 |> List.filter (fun (id, _) -> not (List.exists (fun (id', _) -> Handle.eq id id') hs2))

  let to_list (hyps : t) = hyps
  let of_list (hyps : t) = hyps
end

type pregoal = { g_env : env; g_hyps : Hyps.t; g_goal : form }
type pregoals = pregoal list
type goal = { g_id : Handle.t; g_pregoal : pregoal }

type meta = < > Js_of_ocaml.Js.t

type proof =
  { p_goals : (Handle.t, goal) Map.t
        (** A map from goal handles to goals. Contains only the opened (i.e. currently active) goals. *)
  ; p_meta : (Handle.t, < > Js.t) Map.t ref  (** Metadata associated to each goal. *)
  ; p_db : LemmaDB.t  (** The lemma database. *)
  ; p_hm : Hidmap.hidmap
  }


let mk_hyp ?(src : Handle.t option) ?(gen : int = 0) form =
  { h_src = src; h_gen = gen; h_form = form }

let hidmap proof = proof.p_hm

let init (env : env) (hyps : form list) (goal : form) =
  Form.recheck env goal;
  List.iter (Form.recheck env) hyps;

  let uid = Handle.fresh () in
  let g_hyps =
    List.fold_left (fun hs f -> Hyps.add hs (Handle.fresh ()) (mk_hyp f)) Hyps.empty hyps
  in
  let goal = { g_id = uid; g_pregoal = { g_env = env; g_hyps; g_goal = goal } } in

  { p_goals = Map.singleton uid goal
  ; p_meta = ref Map.empty
  ; p_db = LemmaDB.empty env
  ; p_hm = Hidmap.empty
  }

let ginit (hm : Hidmap.hidmap) (pregoals : pregoal list) : proof =
  (* Make sure the goals all typecheck. *)
  let check { g_env; g_hyps; g_goal } =
    Form.recheck g_env g_goal;
    Hyps.iter (fun hyp -> Form.recheck g_env hyp.h_form) g_hyps
  in
  List.iter check pregoals;

  (* Assign a handle to each goal. *)
  let p_goals =
    List.fold_left
      (fun map g_pregoal ->
        let g_id = Handle.fresh () in
        Map.add g_id { g_id; g_pregoal } map)
      Map.empty pregoals
  in

  { p_goals; p_meta = ref Map.empty; p_db = LemmaDB.empty Env.empty; p_hm = hm }

let get_db (proof : proof) = proof.p_db
let set_db (proof : proof) (db : LemmaDB.t) = { proof with p_db = db }

let set_meta (proof : proof) (id : Handle.t) (meta : meta option) : unit =
  match meta with
  | None -> proof.p_meta := Map.remove id !(proof.p_meta)
  | Some meta -> proof.p_meta := Map.add id meta !(proof.p_meta)

let get_meta (proof : proof) (id : Handle.t) : meta option =
  Map.Exceptionless.find id !(proof.p_meta)

let closed (proof : proof) = Map.is_empty proof.p_goals
let opened (proof : proof) = Map.keys proof.p_goals |> List.of_enum

let byid (proof : proof) (id : Handle.t) : pregoal =
  let goal = Option.get_exn (Map.Exceptionless.find id proof.p_goals) (InvalidGoalId id) in
  goal.g_pregoal

type subgoal = (Handle.t option * form list) list * form

module Translate = struct
  open Api
  open Fo.Translate
  open Hidmap
  open State

  let of_hyp ((hd, { h_form; _ }) : Handle.t * hyp) : Logic_t.hyp State.t =
    let* h_id = find hd in
    return Logic_t.{ h_id; h_form = of_form h_form }

  let of_hyps (hyps : Hyps.t) : Logic_t.hyp list State.t =
    hyps |> Hyps.to_list
    |> fold
         (fun hyps hyp ->
           let* h = of_hyp hyp in
           return (hyps @ [ h ]))
         []

  let to_hyp (Logic_t.{ h_id; h_form } : Logic_t.hyp) : (Handle.t * hyp) State.t =
    let* hd = push h_id in
    return (hd, mk_hyp (to_form h_form))

  let to_hyps (hyps : Logic_t.hyp list) : Hyps.t State.t =
    let* hyps =
      fold
        (fun hyps hyp ->
          let* h = to_hyp hyp in
          return (hyps @ [ h ]))
        [] hyps
    in
    hyps |> Hyps.of_list |> return

  let export_goal (({ g_env; g_hyps; g_goal }, hm) : pregoal * hidmap) : Logic_t.goal =
    Logic_t.{ g_env = of_env g_env; g_hyps = run (of_hyps g_hyps) hm; g_concl = of_form g_goal }

  let import_goal (Logic_t.{ g_env; g_hyps; g_concl } : Logic_t.goal) : pregoal * hidmap =
    let g_env, g_hyps, hm =
      HandleMap.empty
      |> run
           (let* env = to_env g_env in
            let* hyps = to_hyps g_hyps in
            let* hm = get in
            return (env, hyps, hm))
    in
    ({ g_env; g_hyps; g_goal = to_form g_concl }, hm)
end

module Tactics = struct

  exception TacticNotApplicable


let xprogress (pr : proof) (id : Handle.t) (subs : pregoals) =
  (* Promote the pregoals to actual goals. *)
  let subs =
    let for1 sub =
      let hyps = Hyps.bump sub.g_hyps in
      let sub = { sub with g_hyps = hyps } in
      { g_id = Handle.fresh (); g_pregoal = sub }
    in
    List.map for1 subs
  in

  (* The handles of the new goals. *)
  let g_new = List.map (fun x -> x.g_id) subs in

  (* The new goals get the same metadata as the old goal. *)
  let meta =
    match Map.Exceptionless.find id !(pr.p_meta) with
    | None -> !(pr.p_meta)
    | Some meta -> List.fold_left (fun map id -> Map.add id meta map) !(pr.p_meta) g_new
  in

  (* Remove the old goal and add the new goals. *)
  let p_goals =
    pr.p_goals |> Map.remove id |> List.fold_right (fun sub map -> Map.add sub.g_id sub map) subs
  in
  (* Don't forget to return the handles of the new goals. *)
  (g_new, { pr with p_goals; p_meta = ref meta })

let sgprogress (goal : pregoal) ?(clear = false) (subs : subgoal list) =
  let for1 (newlc, concl) =
    let subfor1 hyps (hid, newlc) =
      let hyps =
        Option.fold (fun hyps hid -> if clear then Hyps.remove hyps hid else hyps) hyps hid
      in
      let hsrc = if clear then None else hid in

      let hyps =
        List.fold_left
          (fun hyps newh -> Hyps.add hyps (Handle.fresh ()) (mk_hyp ?src:hsrc newh))
          hyps newlc
      in

      hyps
    in

    let hyps = List.fold_left subfor1 goal.g_hyps newlc in
    { g_env = goal.g_env; g_hyps = hyps; g_goal = concl }
  in

  List.map for1 subs


  let add_local (goal : pregoal) ((name, ty, body) : string * Fo.type_ * Fo.expr option) : pregoal =
    Option.map_default (Fo.Form.erecheck goal.g_env ty) () body;

    let g_env = Fo.Vars.push goal.g_env (name, (ty, body)) in
    let g_env = Fo.Vars.map g_env (Option.map (Fo.Form.e_shift (name, 0))) in

    let g_hyps =
      Hyps.(map (fun h -> { h with h_form = Form.f_shift (name, 0) h.h_form }) goal.g_hyps)
    in

    let g_goal = Form.f_shift (name, 0) goal.g_goal in

    { g_env; g_hyps; g_goal }

  let add_local_def proof ~goal_id (name, ty, body) =
    let new_goal = add_local (byid proof goal_id) (name, ty, Some body) in
    snd @@ xprogress proof goal_id [ new_goal ]

  let ivariants proof ~goal_id =
    match (byid proof goal_id).g_goal with
    | FPred ("_EQ", _) -> [ "reflexivity" ]
    | FTrue -> [ "constructor" ]
    | FConn (`And, _) -> [ "split" ]
    | FConn (`Or, _) -> [ "left"; "right" ]
    | FConn (`Imp, _) -> [ "intro" ]
    | FConn (`Equiv, _) -> [ "split" ]
    | FConn (`Not, _) -> [ "intro" ]
    | FBind (`Forall, _, _, _) -> [ "intro" ]
    | FBind (`Exist, _, _, _) -> [ "exists" ]
    | _ -> []

  let evariants proof ~goal_id ~hyp_id =
    match (Hyps.byid (byid proof goal_id).g_hyps hyp_id).h_form with
    | FPred ("_EQ", _) -> [ "rewrite->"; "rewrite<-" ]
    | FTrue -> [ "destruct" ]
    | FFalse -> [ "destruct" ]
    | FConn (`And, _) -> [ "destruct" ]
    | FConn (`Or, _) -> [ "destruct" ]
    | FConn (`Imp, _) -> [ "apply" ]
    | FConn (`Not, _) -> [ "destruct" ]
    | FBind (`Exist, _, _, _) -> [ "destruct" ]
    | _ -> []

  let generalize proof ~goal_id ~hyp_id =
    let goal = byid proof goal_id in
    let hyp = (Hyps.byid goal.g_hyps hyp_id).h_form in

    snd
    @@ xprogress proof goal_id
         [ { g_env = goal.g_env
           ; g_hyps = Hyps.remove goal.g_hyps hyp_id
           ; g_goal = FConn (`Imp, [ hyp; goal.g_goal ])
           }
         ]

  let move proof ~goal_id ~hyp_id ~dest_id =
    let goal = byid proof goal_id in
    let hyps = Hyps.move goal.g_hyps hyp_id dest_id in

    snd @@ xprogress proof goal_id [ { goal with g_hyps = hyps } ]
end
