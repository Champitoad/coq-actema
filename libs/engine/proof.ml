(* -------------------------------------------------------------------- *)
open Utils
open Fo

(* -------------------------------------------------------------------- *)
module Handle : sig
  type t = private int

  val fresh : unit -> t
  val eq    : t -> t -> bool
end = struct
  type t = int

  let fresh () : t =
    Utils.Uid.fresh ()

  let eq = ((=) : t -> t -> bool)
end

(* -------------------------------------------------------------------- *)
type pnode = ..

exception InvalidGoalId    of Handle.t
exception SubgoalNotOpened of Handle.t

module Proof : sig
  type proof

  type pregoal = {
    g_env  : env;
    g_hyps : (Handle.t, form) Map.t;
    g_goal : form;
  }

  type pregoals = pregoal list

  val init   : env -> form -> proof
  val closed : proof -> bool
  val opened : proof -> Handle.t list
  val byid   : proof -> Handle.t -> pregoal

  val progress :
    proof -> Handle.t -> pnode -> form list -> proof

  val xprogress :
    proof -> Handle.t -> pnode -> pregoals -> proof
end = struct
  type pregoal = {
    g_env  : env;
    g_hyps : (Handle.t, form) Map.t;
    g_goal : form;
  }

  type pregoals = pregoal list

  type proof = {
    p_root : Handle.t;
    p_maps : (Handle.t, goal) Map.t;
    p_crts : Handle.t list;
    p_frwd : (Handle.t, gdep) Map.t;
    p_bkwd : (Handle.t, gdep) Map.t;
  }

  and goal = pregoal

  and gdep = {
    d_src : Handle.t;
    d_dst : Handle.t list;
    d_ndn : pnode;
  }

  let init (env : env) (goal : form) =
    Form.recheck env goal;

    let uid  = Handle.fresh () in
    let root = {
      g_env  = env;
      g_hyps = Map.empty;
      g_goal = goal;
    } in

    { p_root = uid;
      p_maps = Map.singleton uid root;
      p_crts = [uid];
      p_frwd = Map.empty;
      p_bkwd = Map.empty; }

  let closed (proof : proof) =
    List.is_empty proof.p_crts

  let opened (proof : proof) =
    proof.p_crts

  let byid (proof : proof) (id : Handle.t) =
    Option.get_exn
      (Map.Exceptionless.find id proof.p_maps)
      (InvalidGoalId id)

  let xprogress (pr : proof) (id : Handle.t) (pn : pnode) (sub : pregoals) =
    let _goal = byid pr id in
    let nsub  = List.length sub in
    let sids  = List.init nsub (ueta Handle.fresh)  in

    let gr, _, go =
      try  List.pivot (Handle.eq id) pr.p_crts
      with Invalid_argument _ -> raise (SubgoalNotOpened id) in

    let dep = { d_src = id; d_dst = sids; d_ndn = pn; } in

    { pr with
        p_maps = List.fold_right2 Map.add sids sub pr.p_maps;
        p_crts = gr @ sids @ go;
        p_frwd = Map.add id dep pr.p_frwd;
        p_bkwd = List.fold_right (Map.add^~ dep) sids pr.p_bkwd; }

  let progress (pr : proof) (id : Handle.t) (pn : pnode) (sub : form list) =
    let goal = byid pr id in
    let sub  = List.map (fun x -> { goal with g_goal = x }) sub in
    xprogress pr id pn sub
end

(* -------------------------------------------------------------------- *)
exception TacticNotApplicable

module CoreLogic : sig
  type targ   = Proof.proof * Handle.t
  type tactic = targ -> Proof.proof

  val split  : tactic
  val left   : tactic
  val right  : tactic
end = struct
  type targ   = Proof.proof * Handle.t
  type tactic = targ -> Proof.proof

  type pnode += TSplit

  let split ((pr, id) : targ) =
    match (Proof.byid pr id).g_goal with
    | FConn (`And, [f1; f2]) ->
        Proof.progress pr id TSplit [f1; f2]
    | _ -> raise TacticNotApplicable

  type pnode += TLeft

  let left ((pr, id) : targ) =
    match (Proof.byid pr id).g_goal with
    | FConn (`And, [f; _]) ->
        Proof.progress pr id TLeft [f]
    | _ -> raise TacticNotApplicable

  type pnode += TRight

  let right ((pr, id) : targ) =
    match (Proof.byid pr id).g_goal with
    | FConn (`And, [_; f]) ->
        Proof.progress pr id TRight [f]
    | _ -> raise TacticNotApplicable

end
