(* -------------------------------------------------------------------- *)
open Utils
open Fo

(* -------------------------------------------------------------------- *)
module Handle : sig
  type t = private int

  val ofint : int -> t
  val fresh : unit -> t
  val eq    : t -> t -> bool
end = struct
  type t = int

  let fresh () : t =
    Utils.Uid.fresh ()

  let ofint (i : int) : t =
    i

  let eq = ((=) : t -> t -> bool)
end

(* -------------------------------------------------------------------- *)
type pnode = ..

exception InvalidGoalId    of Handle.t
exception InvalidHyphId    of Handle.t
exception SubgoalNotOpened of Handle.t

module Proof : sig
  type proof

  type hyps = (Handle.t, Handle.t option * form) Map.t

  module Hyps : sig
    val byid : hyps -> Handle.t -> Handle.t option * form
  end

  type pregoal = {
    g_env  : env;
    g_hyps : hyps;
    g_goal : form;
  }

  type pregoals = pregoal list

  val init   : env -> form -> proof
  val closed : proof -> bool
  val opened : proof -> Handle.t list
  val byid   : proof -> Handle.t -> pregoal

  val progress :
    proof -> Handle.t -> pnode -> form list -> proof

  val sprogress :
    proof -> Handle.t -> pnode ->
      ((Handle.t option * form list) list * form) list -> proof

  val xprogress :
    proof -> Handle.t -> pnode -> pregoals -> proof
end = struct
  type hyps = (Handle.t, Handle.t option * form) Map.t

  type pregoal = {
    g_env  : env;
    g_hyps : hyps;
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

  module Hyps = struct
    let byid (hyps : hyps) (id : Handle.t) =
      Option.get_exn
        (Map.Exceptionless.find id hyps)
        (InvalidHyphId id)
  end

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

  let sprogress (pr : proof) (id : Handle.t) (pn : pnode) sub =
    let goal = byid pr id in

    let for1 (newlc, concl) =
      let subfor1 hyps (hid, newlc) =
        let hyps =
          Option.fold (fun hyps hid ->
            let _h = snd (Hyps.byid hyps hid) in
            Map.remove hid hyps)
          hyps hid in
        let hyps = List.fold_left (fun hyps newh ->
            Map.add (Handle.fresh ()) (None, newh) hyps)
          hyps newlc
        in hyps in

      let hyps = List.fold_left subfor1 goal.g_hyps newlc in
      { goal with g_hyps = hyps; g_goal = concl; }

    in xprogress pr id pn (List.map for1 sub)      

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

  val intro     : ?variant:int -> tactic
  val elim      : Handle.t -> tactic
  val ivariants : targ -> string list
end = struct
  type targ   = Proof.proof * Handle.t
  type tactic = targ -> Proof.proof

  type pnode += TIntro

  let intro ?(variant = 0) ((pr, id) : targ) =
    match variant, (Proof.byid pr id).g_goal with
    | 0, FConn (`And, [f1; f2]) ->
        Proof.progress pr id TIntro [f1; f2]

    | 0, FConn (`Imp, [f1; f2]) ->
        Proof.sprogress pr id TIntro
          [[None, [f1]], f2]

    | 0, FConn (`Equiv, [f1; f2]) ->
        Proof.progress pr id TIntro
          [Form.f_imp f1 f2; Form.f_imp f2 f1]

    | 0, FConn (`Or, [f; _]) ->
        Proof.progress pr id TIntro [f]

    | 1, FConn (`Or, [f; _]) ->
        Proof.progress pr id TIntro [f]

    | 0, FConn (`Not, [f]) ->
        Proof.sprogress pr id TIntro
          [[None, [f]], FFalse]

    | 0, FTrue ->
        Proof.progress pr id TIntro []

    | _ -> raise TacticNotApplicable

  type pnode += TElim of Handle.t

  let elim (h : Handle.t) ((pr, id) : targ) =
    let gl = Proof.byid pr id in
    let hy = snd (Proof.Hyps.byid gl.g_hyps h) in

    let pre, hy =
      let rec doit acc = function
        | FConn (`Imp, [f1; f2]) -> doit (f1 :: acc) f2
        | f -> (List.rev acc, f)
      in doit [] hy in

    let subs = List.map (fun f -> [Some h, []], f) pre in

    if Form.equal hy gl.g_goal then
      Proof.sprogress pr id (TElim id) subs
    else

    match hy with
    | FConn (`And, [f1; f2]) ->
        Proof.sprogress pr id (TElim id)
          (subs @ [[Some h, [f1; f2]], gl.g_goal])

    | FConn (`Or, [f1; f2]) ->
        Proof.sprogress pr id (TElim id)
          (subs @ [[Some h, [f1]], gl.g_goal;
                   [Some h, [f2]], gl.g_goal])

    | FConn (`Equiv, [f1; f2]) ->
        Proof.sprogress pr id (TElim id)
          (subs @ [[Some h, [Form.f_imp f1 f2; Form.f_imp f2 f1]], gl.g_goal])

    | FConn (`Not, [f]) ->
        Proof.sprogress pr id (TElim id)
          (subs @ [[Some h, []], f])

    | FFalse ->
        Proof.sprogress pr id (TElim id) subs

    | FTrue ->
        Proof.sprogress pr id (TElim id)
          (subs @ [[Some h, []], gl.g_goal])

    | _ -> raise TacticNotApplicable

  let ivariants ((pr, id) : targ) =
    match (Proof.byid pr id).g_goal with
    | FConn (`And  , _) -> ["And-intro"]
    | FConn (`Or   , _) -> ["Or-intro-L"; "Or-intro-R"]
    | FConn (`Imp  , _) -> ["Imp-intro"]
    | FConn (`Equiv, _) -> ["Equiv-intro"]
    | FConn (`Not  , _) -> ["Not-intro"]

    | _ -> []
end

