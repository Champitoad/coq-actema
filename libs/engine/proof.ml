(* -------------------------------------------------------------------- *)
open Utils
open Fo

(* -------------------------------------------------------------------- *)
module Handle : sig
  type t = private int

  val ofint : int -> t
  val fresh : unit -> t
  val eq    : t -> t -> bool
  val toint : t -> int
end = struct
  type t = int

  let fresh () : t =
    Utils.Uid.fresh ()

  let ofint (i : int) : t =
    i

  let toint (t : t) : int =
    t

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

  type meta = < > Js_of_ocaml.Js.t

  val set_meta : proof -> Handle.t -> meta option -> unit
  val get_meta : proof -> Handle.t -> meta option

  val progress :
    proof -> Handle.t -> pnode -> form list -> proof

  val sprogress :
    proof -> ?clear:bool -> Handle.t -> pnode ->
      ((Handle.t option * form list) list * form) list -> proof

  val xprogress :
    proof -> Handle.t -> pnode -> pregoals -> proof
end = struct
  module Js = Js_of_ocaml.Js

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
    p_meta : (Handle.t, < > Js.t) Map.t ref;
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
      p_bkwd = Map.empty;
      p_meta = ref Map.empty; }

  let closed (proof : proof) =
    List.is_empty proof.p_crts

  let opened (proof : proof) =
    proof.p_crts

  let byid (proof : proof) (id : Handle.t) =
    Option.get_exn
      (Map.Exceptionless.find id proof.p_maps)
      (InvalidGoalId id)

  type meta = < > Js_of_ocaml.Js.t

  let set_meta (proof : proof) (id : Handle.t) (meta : meta option) : unit =
    match meta with
    | None ->
        proof.p_meta := Map.remove id !(proof.p_meta)
        
    | Some meta ->
        proof.p_meta := Map.add id meta !(proof.p_meta)

  let get_meta (proof : proof) (id : Handle.t) : meta option =
    Map.Exceptionless.find id !(proof.p_meta)

  let xprogress (pr : proof) (id : Handle.t) (pn : pnode) (sub : pregoals) =
    let _goal = byid pr id in
    let nsub  = List.length sub in
    let sids  = List.init nsub (ueta Handle.fresh)  in

    let gr, _, go =
      try  List.pivot (Handle.eq id) pr.p_crts
      with Invalid_argument _ -> raise (SubgoalNotOpened id) in

    let dep = { d_src = id; d_dst = sids; d_ndn = pn; } in

    let meta =
      match Map.Exceptionless.find id !(pr.p_meta) with
      | None ->
          !(pr.p_meta)

      | Some meta ->
          List.fold_left
            (fun map id -> Map.add id meta map)
            !(pr.p_meta) sids
    in

    { pr with
        p_maps = List.fold_right2 Map.add sids sub pr.p_maps;
        p_crts = gr @ sids @ go;
        p_frwd = Map.add id dep pr.p_frwd;
        p_bkwd = List.fold_right (Map.add^~ dep) sids pr.p_bkwd;
        p_meta = ref meta; }

  let sprogress (pr : proof) ?(clear = false) (id : Handle.t) (pn : pnode) sub =
    let goal = byid pr id in

    let for1 (newlc, concl) =
      let subfor1 hyps (hid, newlc) =
        let hyps =
          Option.fold (fun hyps hid ->
            let _h = snd (Hyps.byid hyps hid) in
            if clear then Map.remove hid hyps else hyps)
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
  type path   = string

  val intro     : ?variant:int -> tactic
  val elim      : ?clear:bool -> Handle.t -> tactic
  val ivariants : targ -> string list
  val forward   : (Handle.t * Handle.t) -> tactic

  type asource = [
    | `Click of path
    | `DnD   of adnd
  ]

  and adnd = { source : path; destination : path; }

  type action = Handle.t * [
    | `Elim    of Handle.t
    | `Intro   of int
    | `Forward of Handle.t * Handle.t
  ]

  exception InvalidPath of path

  val actions : Proof.proof -> asource -> (string * path list * action) list
  val apply   : Proof.proof -> action -> Proof.proof
end = struct
  type targ   = Proof.proof * Handle.t
  type tactic = targ -> Proof.proof
  type path   = string

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

    | 1, FConn (`Or, [_; f]) ->
        Proof.progress pr id TIntro [f]

    | 0, FConn (`Not, [f]) ->
        Proof.sprogress pr id TIntro
          [[None, [f]], FFalse]

    | 0, FTrue ->
        Proof.progress pr id TIntro []

    | _ -> raise TacticNotApplicable

  type pnode += TElim of Handle.t

  let elim ?clear (h : Handle.t) ((pr, id) : targ) =
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
        Proof.sprogress pr ?clear id (TElim id)
          (subs @ [[Some h, [f1; f2]], gl.g_goal])

    | FConn (`Or, [f1; f2]) ->
        Proof.sprogress pr ?clear id (TElim id)
          (subs @ [[Some h, [f1]], gl.g_goal;
                   [Some h, [f2]], gl.g_goal])

    | FConn (`Equiv, [f1; f2]) ->
        Proof.sprogress pr ?clear id (TElim id)
          (subs @ [[Some h, [Form.f_imp f1 f2; Form.f_imp f2 f1]], gl.g_goal])

    | FConn (`Not, [f]) ->
        Proof.sprogress pr ?clear id (TElim id)
          (subs @ [[Some h, []], f])

    | FFalse ->
        Proof.sprogress pr ?clear id (TElim id) subs

    | FTrue ->
        Proof.sprogress pr ?clear id (TElim id)
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

  type pnode += TForward of Handle.t * Handle.t

  let forward (hsrc, hdst) ((pr, id) : targ) =
    let gl  = Proof.byid pr id in
    let src = snd (Proof.Hyps.byid gl.g_hyps hsrc) in
    let dst = snd (Proof.Hyps.byid gl.g_hyps hdst) in

    match dst with
    | FConn (`Imp, [f; f']) when Form.equal f src ->
        Proof.sprogress pr ~clear:true id (TForward (hsrc, hdst))
          ([[Some hdst, [f']], gl.g_goal])

    | _ -> raise TacticNotApplicable

  type action = Handle.t * [
    | `Elim    of Handle.t
    | `Intro   of int
    | `Forward of Handle.t * Handle.t
  ]

  exception InvalidPath of path
  exception InvalidFormPath

  let rec subform (f : form) (p : int list) =
    match p with [] -> f | i :: subp ->

    match f with
    | FConn (_, fs) ->
        let subf =
          try  List.nth fs i
          with Failure _ -> raise InvalidFormPath
        in subform subf subp

    | _ ->
        raise InvalidFormPath

  let ofpath (proof : Proof.proof) (p : path) =
    let hd, i, fs =
      try
        Scanf.sscanf p "%d/%d:%s" (fun x1 x2 x3 -> (x1, x2, x3))
      with
      | Scanf.Scan_failure _
      | End_of_file ->
          raise (InvalidPath p) in

    if hd < 0 || i < 0 then
      raise (InvalidPath p);

    let fs =
      let fs = if fs = "" then [] else String.split_on_char '/' fs in

      try
        List.map int_of_string fs
      with Failure _ -> raise (InvalidPath p) in

      if List.exists (fun x -> x < 0) fs then
        raise (InvalidPath p);

    let goal =
      try  Proof.byid proof (Handle.ofint hd)
      with InvalidGoalId _ -> raise (InvalidPath p) in

    let target, subf =
      try
        match i with
        | _ when i <= 0 ->
            (`C goal.Proof.g_goal, subform goal.Proof.g_goal fs)
  
        | _ -> begin
            try
              let rp = Handle.ofint i in
              let (_, hf) as hyd =
                Proof.Hyps.byid goal.Proof.g_hyps (Handle.ofint i) in
              (`H (rp, hyd), subform hf fs)
            with InvalidHyphId _ -> raise (InvalidPath p)
          end

      with InvalidFormPath -> raise (InvalidPath p)

    in (goal, Handle.ofint hd, target, (fs, subf))

  type asource = [
    | `Click of path
    | `DnD   of adnd
  ]

  and adnd = { source : path; destination : path; }

  let actions (proof : Proof.proof) (p : asource)
      : (string * path list * action) list
  =
    match p with
    | `Click p -> begin
      let _goal, hd, target, (_fs, _subf) = ofpath proof p in
  
      match target with
      | `C _ -> begin
          let iv = ivariants (proof, hd) in
          let bv = List.length iv <= 1 in
  
          List.mapi
            (fun i x ->
              let hg =
                if   bv
                then Format.sprintf "%d/0:" (Handle.toint hd)
                else Format.sprintf "%d/0:%d" (Handle.toint hd) i in
  
              (x, [hg], (hd, `Intro i)))
            iv
        end
  
      | `H (rp, _) ->
          let hg = Format.sprintf "%d/%d:"
                     (Handle.toint hd) (Handle.toint rp) in
          ["Elim", [hg], (hd, `Elim rp)]
      end

    | `DnD { source = src; destination = dst; } -> begin
      let module E = struct exception Nothing end in

      try
        let _, hd1, tg1, _ = ofpath proof src in
        let _, hd2, tg2, _ = ofpath proof dst in

        if not (Handle.eq hd1 hd2) then
          raise E.Nothing;

        let (tg1, f1), (tg2, f2) =
          match tg1, tg2 with
          | `H (tg1, (_, f1)), `H (tg2, (_, f2)) ->
              ((tg1, f1), (tg2, f2))
          | _ -> raise E.Nothing in

        match f2 with
        | FConn (`Imp, [f; _]) when Form.equal f1 f ->
            let hg = Format.sprintf "%d/%d:0"
                       (Handle.toint hd1) (Handle.toint tg2) in
            ["Forward", [hg], (hd1, `Forward (tg1, tg2))]
            
        | _ ->
            raise E.Nothing

      with E.Nothing -> []
    end

  let apply (proof : Proof.proof) ((hd, a) : action) =
    match a with
    | `Intro variant ->
        intro ~variant (proof, hd)
    | `Elim subhd ->
        elim subhd (proof, hd)
    | `Forward (src, dst) ->
        forward (src, dst) (proof, hd)
end
