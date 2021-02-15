(* -------------------------------------------------------------------- *)
open Utils
open Fo

(* ------------------------------------------------------------------- *)
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

  type hyp = {
    h_src  : Handle.t option;
    h_gen  : int;
    h_form : form;
  }

  val mk_hyp : ?src:Handle.t -> ?gen:int -> form -> hyp

  type hyps

  module Hyps : sig
    val empty   : hyps
    val byid    : hyps -> Handle.t -> hyp
    val add     : hyps -> Handle.t -> hyp -> hyps
    val remove  : hyps -> Handle.t -> hyps
    val move    : hyps -> Handle.t -> Handle.t option -> hyps
    val bump    : hyps -> hyps
    val ids     : hyps -> Handle.t list
    val to_list : hyps -> (Handle.t * hyp) list
  end

  type pregoal = {
    g_env  : env;
    g_hyps : hyps;
    g_goal : form;
  }

  and goal = { g_id: Handle.t; g_pregoal: pregoal; }

  type pregoals = pregoal list

  val init   : env -> form -> proof
  val closed : proof -> bool
  val opened : proof -> Handle.t list
  val byid   : proof -> Handle.t -> pregoal

  type meta = < > Js_of_ocaml.Js.t

  val set_meta : proof -> Handle.t -> meta option -> unit
  val get_meta : proof -> Handle.t -> meta option

  val sgprogress :
    pregoal -> ?clear:bool ->
      ((Handle.t option * form list) list * form) list -> pregoals

  val progress :
    proof -> Handle.t -> pnode -> form list -> proof

  val sprogress :
    proof -> ?clear:bool -> Handle.t -> pnode ->
      ((Handle.t option * form list) list * form) list -> proof

  val xprogress :
    proof -> Handle.t -> pnode -> pregoals -> proof
end = struct
  module Js = Js_of_ocaml.Js

  type hyp = {
    h_src  : Handle.t option;
    h_gen  : int;
    h_form : form;
  }

  module Hyps : sig
    type hyps

    val empty   : hyps
    val byid    : hyps -> Handle.t -> hyp
    val add     : hyps -> Handle.t -> hyp -> hyps
    val remove  : hyps -> Handle.t -> hyps
    val move    : hyps -> Handle.t -> Handle.t option -> hyps
    val bump    : hyps -> hyps
    val ids     : hyps -> Handle.t list
    val to_list : hyps -> (Handle.t * hyp) list
  end = struct
    type hyps = (Handle.t * hyp) list

    let empty : hyps =
      []

    let byid (hyps : hyps) (id : Handle.t) =
      Option.get_exn
        (List.Exceptionless.assoc id hyps)
        (InvalidHyphId id)

    let add (hyps : hyps) (id : Handle.t) (h : hyp) : hyps =
      assert (Option.is_none (List.Exceptionless.assoc id hyps));
      (id, h) :: hyps

    let remove (hyps : hyps) (id : Handle.t) : hyps =
      List.filter (fun (x, _) -> not (Handle.eq x id)) hyps

    let move (hyps : hyps) (from : Handle.t) (before : Handle.t option) =
      let tg   = byid hyps from in
      let hyps = remove hyps from in

      match before with
      | None ->
          (from, tg) :: hyps

      | Some before ->
          let pos, _ =
            Option.get_exn
              (List.Exceptionless.findi (fun _ (x, _) -> Handle.eq x before) hyps)
              (InvalidHyphId before) in

          let post, pre = List.split_at (1+pos) hyps in

          post @ (from, tg) :: pre

    let bump (hyps : hyps) : hyps =
      List.map (fun (id, h) -> (id, { h with h_gen = h.h_gen + 1 })) hyps

    let ids (hyps : hyps) =
      List.fst hyps

    let to_list (hyps : hyps) =
      hyps
  end

  type hyps = Hyps.hyps

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

  and goal = { g_id: Handle.t; g_pregoal: pregoal; }

  and gdep = {
    d_src : Handle.t;
    d_dst : Handle.t list;
    d_ndn : pnode;
  }

  let mk_hyp ?(src : Handle.t option) ?(gen : int = 0) form =
    { h_src = src; h_gen = gen; h_form = form; }

  let init (env : env) (goal : form) =
    Form.recheck env goal;

    let uid  = Handle.fresh () in
    let root = { g_id = uid; g_pregoal = {
        g_env  = env;
        g_hyps = Hyps.empty;
        g_goal = goal;
      }
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

  let byid (proof : proof) (id : Handle.t) : pregoal =
    let goal =
      Option.get_exn
        (Map.Exceptionless.find id proof.p_maps)
        (InvalidGoalId id)
    in goal.g_pregoal

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

    let sub =
      let for1 sub =
        let hyps = Hyps.bump sub.g_hyps in
        let sub  = { sub with g_hyps = hyps } in
        { g_id = Handle.fresh (); g_pregoal = sub; }
      in List.map for1 sub in

    let sids = List.map (fun x -> x.g_id) sub in

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

    let map =
      List.fold_right
        (fun sub map -> Map.add sub.g_id sub map)
        sub pr.p_maps in

    { pr with
        p_maps = map;
        p_crts = gr @ sids @ go;
        p_frwd = Map.add id dep pr.p_frwd;
        p_bkwd = List.fold_right (Map.add^~ dep) sids pr.p_bkwd;
        p_meta = ref meta; }

  let sgprogress (goal : pregoal) ?(clear = false) sub =
    let for1 (newlc, concl) =
      let subfor1 hyps (hid, newlc) =
        let hyps =
          Option.fold (fun hyps hid ->
            let _h = (Hyps.byid hyps hid).h_form in
            if clear then Hyps.remove hyps hid else hyps)
          hyps hid in
        let hsrc = if clear then None else hid in

        let hyps = List.fold_left (fun hyps newh ->
            Hyps.add hyps (Handle.fresh ()) (mk_hyp ?src:hsrc newh))
          hyps newlc
        in hyps in

      let hyps = List.fold_left subfor1 goal.g_hyps newlc in
      { g_env = goal.g_env; g_hyps = hyps; g_goal = concl; }

    in List.map for1 sub

  let sprogress (pr : proof) ?(clear = false) (id : Handle.t) (pn : pnode) sub =
    let goal = byid pr id in
    let sub = sgprogress goal ~clear sub in
    xprogress pr id pn sub

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

  type path        = string
  type ipath       = { root : int; ctxt : int; sub : int list; }
  type link        = ipath * ipath
  type hyperlink   = ipath list * ipath list

  val ipath_of_path : path -> ipath

  type item   = [`C of form | `H of Handle.t * Proof.hyp ]
  type pol    = Pos | Neg | Sup

  val cut        : Fo.form -> tactic
  val add_local  : string * Fo.type_ * Fo.expr -> tactic
  val generalize : Handle.t -> tactic
  val move       : Handle.t -> Handle.t option -> tactic
  val intro      : ?variant:(int * (expr * type_) option) -> tactic
  val elim       : ?clear:bool -> Handle.t -> tactic
  val ivariants  : targ -> string list
  val forward    : (Handle.t * Handle.t * int list * Form.Subst.subst) -> tactic

  type asource =
    { kind : asource_kind; selection : selection; }

  and asource_kind = [
    | `Click of ipath
    | `DnD   of adnd
  ]

  and adnd = {
    source      : ipath;
    destination : ipath option;
  }

  and selection = ipath list

  type osource = [
    | `Click of ipath
    | `DnD   of link
  ]

  val path_of_ipath : ipath -> path

  type linkaction = [
    | `Nothing
    | `Both of linkaction * linkaction
    | `Subform of Form.Subst.subst * Form.Subst.subst
    | `Rewrite of expr * expr * ipath list
  ]

  type action = Handle.t * [
    | `Elim      of Handle.t
    | `Intro     of int
    | `Forward   of Handle.t * Handle.t * (int list) * Form.Subst.subst 
    | `DisjDrop  of Handle.t * form list
    | `ConjDrop  of Handle.t
    | `Hyperlink of hyperlink * linkaction list
  ]

  exception InvalidPath of path
  exception InvalidSubFormPath of int list
  exception InvalidSubExprPath of int list

  val actions : Proof.proof -> asource ->
                  (string * ipath list * osource * action) list
 (* string : doc
    ipath list : surbrillance
    osource 
 *)

  val apply   : Proof.proof -> action -> Proof.proof
end = struct
  type targ   = Proof.proof * Handle.t
  type tactic = targ -> Proof.proof
  
  let id_tac : tactic =
    fst
  
  let then_tac (t1 : tactic) (t2 : tactic) : tactic =
    fun targ ->
      let pr = t1 targ in
      let hd = List.hd (Proof.opened pr) in
      t2 (pr, hd)

  let thenl_tac (t1 : tactic) (t2 : tactic) : tactic =
    fun targ ->
      let pr = t1 targ in
      List.fold_left (uncurry t2) pr (Proof.opened pr)

  let prune_premisses =
    let rec doit acc = function
      | FConn (`Imp, [f1; f2]) -> doit (f1 :: acc) f2
      | f -> (List.rev acc, f)
    in fun f -> doit [] f

  let prune_premisses_fa =
    let rec doit i acc s = function
      | FConn (`Imp, [f1; f2]) -> doit i ((i, f1) :: acc) s f2
      | FBind (`Forall, x, _, f) -> doit (i+1) acc ((x,Sflex)::s) f 
      | f -> (List.rev acc, f, s)
    in fun f ->

    let pre, hy, s  = doit 0 [] [] f in 

    (pre, hy, Form.Subst.oflist s)

  let prune_premisses_ex =
    let rec doit i acc s = function
      | FBind (`Exist, x, _, f) -> doit (i+1) acc ((x, Sflex)::s) f
      | f -> (List.rev acc, f, s)
    in fun f ->

    let pre, hy, s = doit 0 [] [] f in

    (pre, hy, Form.Subst.oflist s)
	
  let rec remove_form f = function
      | [] -> raise TacticNotApplicable
      | g::l when Form.f_equal g f -> l
      | g::l -> g::(remove_form f l)

  type pnode += TIntro of (int * (expr * type_) option)

  let intro ?(variant = (0, None)) ((pr, id) : targ) =
    let pterm = TIntro variant in

    match variant, (Proof.byid pr id).g_goal with
    | (0, None), FPred ("_EQ", [e1; e2]) when Form.e_equal e1 e2 ->
        Proof.progress pr id pterm []

    | (0, None), FConn (`And, [f1; f2]) ->
        Proof.progress pr id pterm [f1; f2]

    | (0, None), FConn (`Imp, [f1; f2]) ->
        Proof.sprogress pr id pterm
          [[None, [f1]], f2]

    | (0, None), FConn (`Equiv, [f1; f2]) ->
        Proof.progress pr id pterm
          [Form.f_imp f1 f2; Form.f_imp f2 f1]

    | (i, None), (FConn (`Or, _) as f) ->
        let fl = Form.flatten_disjunctions f in
        let g = List.nth fl i in
        Proof.progress pr id pterm [g]

    | (0, None), FConn (`Not, [f]) ->
        Proof.sprogress pr id pterm [[None, [f]], FFalse]

    | (0, None), FTrue ->
        Proof.progress pr id pterm []

    | (0, None), FBind (`Forall, x, xty, body) ->
        let goal = Proof.byid pr id in
        let y = Vars.fresh ~basename:x goal.g_env () in
        let body = Form.Subst.f_apply1 (x, 0) (EVar (y, 0)) body in
        let goal = { goal with
          g_env  = Vars.push goal.g_env (y, xty, None);
          g_goal = body;
        }
        in Proof.xprogress pr id pterm [goal]

    | (0, Some (e, ety)), FBind (`Exist, x, xty, body) -> begin
        let goal = Proof.byid pr id in

        Fo.Form.erecheck goal.g_env ety e;
        if not (Form.t_equal xty ety) then
          raise TacticNotApplicable;
        let goal = Fo.Form.Subst.f_apply1 (x, 0) e body in
        Proof.sprogress pr id pterm [[], goal]
      end

    | _ -> raise TacticNotApplicable

  type pnode += OrDrop of Handle.t

  let or_drop (h : Handle.t) ((pr, id) : targ) hl =
    let gl   = Proof.byid pr id in
    let _hy  = (Proof.Hyps.byid gl.g_hyps h).h_form in
    let _gll = Form.flatten_disjunctions gl.g_goal in
    Proof.sprogress pr id (OrDrop id) hl

  type pnode += AndDrop of Handle.t

  let and_drop (h : Handle.t) ((pr, id) : targ) =
    let gl  = Proof.byid pr id in
    let hy  = (Proof.Hyps.byid gl.g_hyps h).h_form in
    let gll = Form.flatten_conjunctions gl.g_goal in
    let ng  = Form.f_ands (remove_form hy gll) in

    Proof.sprogress pr id (AndDrop id) [[None, []], ng]

  type pnode += TElim of Handle.t

  let core_elim ?clear (h : Handle.t) ((pr, id) : targ) =
    let _ = clear in            (* FIXME *)
    let result = ref ([]) in 
    let gl = Proof.byid pr id in
    let hyp = (Proof.Hyps.byid gl.g_hyps h).h_form in

    if Form.f_equal hyp gl.g_goal
    then result := [(TElim id), `S []] 
    else ();

    let pre, hy, s = prune_premisses_fa hyp in
    begin match Form.f_unify LEnv.empty s [(hy, gl.g_goal)] with
    | Some s when Form.Subst.is_complete s ->  
        let pres = List.map
        (fun (i, x) -> [Some h, []], (Form.Subst.f_iter s i x)) pre in
        result :=  ((TElim id), `S pres)::!result
    | Some _ -> () (* "incomplete match" *)
    | _ -> ();
    end;
    let subs = List.map (fun (_, f) -> [Some h, []], f) pre in
    begin match hy with
    | FConn (`And, [f1; f2]) ->
        result := ((TElim id), `S (subs @ [[Some h, [f1; f2]], gl.g_goal])) :: !result
    (* clear *) 
    | FConn (`Or, [f1; f2]) ->
        result := ((TElim id), 
                   `S (subs @ [[Some h, [f1]], gl.g_goal;
                           [Some h, [f2]], gl.g_goal])) :: !result
    | FConn (`Equiv, [f1; f2]) ->
        result := ((TElim id),
                   `S (subs @ [[Some h, [Form.f_imp f1 f2;
                                      Form.f_imp f2 f1]], gl.g_goal])) :: !result
    | FConn (`Not, [f]) ->
        result := ((TElim id), 
                   `S (subs @ [[Some h, []], f])) :: !result
    | FFalse -> result := ((TElim id), `S subs) :: !result
    | FBind (`Exist, x, ty, f) ->
        let y = Vars.fresh ~basename:x gl.g_env () in
        let hyp = Form.Subst.f_apply1 (x, 0) (EVar (y, 0)) f in
        
        let g_hyps = Proof.Hyps.remove gl.g_hyps h in
        let g_hyps = Proof.(Hyps.add g_hyps h (mk_hyp hyp)) in
        let goal = Proof.{ gl with
          g_env = Vars.push gl.g_env (y, ty, None);
          g_hyps
        }

        in result := ((TElim id), `X [goal]) :: !result
    | _ -> ()
    end;
    let _ , goal, s = prune_premisses_ex gl.g_goal in
    let pre, hy = prune_premisses hyp in
    let pre = List.map (fun x -> [(Some h), []],x) pre in
    begin match Form.f_unify LEnv.empty s [(hy, goal)] with
    | Some s when Form.Subst.is_complete s ->
        result := ((TElim id), `S pre) :: !result
    | Some _ -> () (* failwith "incomplete ex match" *)
    | None ->
        match goal with
        | FConn (`Or , _) ->
          let gll = Form.flatten_disjunctions goal in
          let rec aux = function
            | [] -> false
            | g::l -> begin match Form.f_unify LEnv.empty s [(hyp, g)] with
                | Some s when Form.Subst.is_complete s -> true
                | _ -> aux l
              end
          in 
          if aux gll 
          then result := ((TElim id), `S []) :: !result
          else ()
        | _ -> ()
    end;
    !result

  let perform l pr id =
    match l with
      | (t, `S l)::_ -> Proof.sprogress pr id t l
      | (t, `X l)::_ -> Proof.xprogress pr id t l
      | _ -> raise TacticNotApplicable
  
  let elim ?clear (h : Handle.t) ((pr, id) : targ) =
    perform (core_elim ?clear h (pr, id)) pr id
	
  let ivariants ((pr, id) : targ) =
    match (Proof.byid pr id).g_goal with
    | FPred ("_EQ", _) -> ["EQ-intro"]
    | FTrue -> ["True-intro"]
    | FConn (`And  , _) -> ["And-intro"]
    | FConn (`Or   , _) as f ->
        let fl = Form.flatten_disjunctions f in
        List.mapi (fun i _ -> "Or-intro-"^(string_of_int i)) fl
    | FConn (`Imp  , _) -> ["Imp-intro"]
    | FConn (`Equiv, _) -> ["Equiv-intro"]
    | FConn (`Not  , _) -> ["Not-intro"]
    | FBind (`Forall, _, _, _) -> ["FA-intro"] 
    | FBind (`Exist, _, _, _) -> ["Ex-intro"]

    | _ -> []

  type pnode += TForward of Handle.t * Handle.t

  let core_forward (hsrc, hdst, p, s) ((pr, id) : targ)  =
    let gl   = Proof.byid pr id in
    let _src = (Proof.Hyps.byid gl.g_hyps hsrc).h_form in
    let dst  = (Proof.Hyps.byid gl.g_hyps hdst).h_form in

    (* Here we eventually should have the call to the proof tactics *)
    let rec build_dest = function
      | ((FBind (`Forall, x, ty, f)), 0::p, ((_, Sflex)::s)) ->
          FBind (`Forall, x, ty, build_dest (f, p, s))
      | ((FBind (`Forall, x, _, f)), 0::p, ((_, (Sbound e))::s)) ->
          build_dest ((Form.Subst.f_apply1 (x, 0) e f), p, s)
      | (FConn (`Imp, [_; f2]), (0::_), s) ->
          Form.Subst.f_apply (Form.Subst.oflist s) f2
      | (FConn (`Imp, [f1; f2]), (1::p), s) ->
          FConn(`Imp, [Form.Subst.f_apply (Form.Subst.oflist s) f1;
          build_dest (f2, p, s)])
      | _ -> failwith "cannot build forward"
    in
    let nf = build_dest (dst, p, s) in

    [ (TForward (hsrc, hdst)), `S [[Some hdst, [nf]], gl.g_goal] ]

  let forward (hsrc, hdst, p, s) ((pr, id) : targ) =
    perform (core_forward (hsrc, hdst, p, Form.Subst.aslist s) (pr, id)) pr id 

  type pnode += TCut of Fo.form * Handle.t

  let cut (form : form) ((proof, hd) : targ) =
    let goal = Proof.byid proof hd in

    Fo.Form.recheck goal.g_env form;

    let subs = [[], form] in
    
    Proof.sprogress proof hd (TCut (form, hd))
      (subs @ [[None, [form]], goal.g_goal])

  type pnode += TDef of (Fo.type_ * Fo.expr) * Handle.t

  let add_local ((name, ty, body) : string * Fo.type_ * Fo.expr) ((proof, hd) : targ) =
    let goal = Proof.byid proof hd in

    Fo.Form.erecheck goal.g_env ty body;

    let env = Fo.Vars.push goal.g_env (name, ty, Some body) in
    
    Proof.xprogress proof hd (TDef ((ty, body), hd)) [{ goal with g_env = env }]

  type pnode += TGeneralize of Handle.t

  let generalize (hid : Handle.t) ((proof, id) : targ) =
    let goal = Proof.byid proof id in
    let hyp  = (Proof.Hyps.byid goal.g_hyps hid).h_form in

    Proof.xprogress proof id (TGeneralize hid)
      [{ g_env  = goal.g_env;
         g_hyps = Proof.Hyps.remove goal.g_hyps hid;
         g_goal = FConn (`Imp, [hyp; goal.g_goal]) } ]

  type pnode += TMove of Handle.t * Handle.t option

  let move (from : Handle.t) (before : Handle.t option) ((proof, id) : targ) =
    let goal    = Proof.byid proof id in
    let _from   = Proof.Hyps.byid goal.g_hyps in (* KEEP *)
    let _before = Option.map (Proof.Hyps.byid goal.g_hyps) before in (* KEEP *)
    let hyps    = Proof.Hyps.move goal.g_hyps from before in

    Proof.xprogress proof id (TMove (from, before))
      [{ goal with g_hyps = hyps }]
  

  (** The [close_with_unit] tactic tries to close the goal either with
      the falsity elimination rule, or the truth introduction rule. *)

  let close_with_unit : tactic =
    fun (proof, g_id as targ) ->

    let open Proof in

    let goal = byid proof g_id in

    (* Truth intro *)
    if goal.g_goal = FTrue then intro targ else

    (* Falsity elim *)
    Hyps.to_list goal.g_hyps
    |>
    List.find_map_opt
      (fun (hd, { h_form = f; _ }) ->
       if f = FFalse then Some (elim hd targ) else None)
    |>
    Option.default proof
    

  (* -------------------------------------------------------------------- *)
  (** Items *)


  type item   = [`C of form | `H of Handle.t * Proof.hyp ]
  

  let form_of_item = function
    | `C f | `H (_, Proof.{ h_form = f; _ }) -> f
    | _ -> raise (Invalid_argument "Expected a formula item")
    
  let expr_of_item = function
    | _ -> raise (Invalid_argument "Expected an expression item")
  
  let term_of_item it =
    try `F (form_of_item it)
    with Invalid_argument _ ->
      try `E (expr_of_item it)
      with Invalid_argument _ ->
        raise (Invalid_argument "Expected an expression or formula item")      


  (* -------------------------------------------------------------------- *)
  (** Paths *)


  type path   = string
  type ipath  = { root : int; ctxt : int; sub : int list; }

  exception InvalidPath of path
  exception InvalidSubFormPath of int list
  exception InvalidSubExprPath of int list

  let direct_subterm (t : term) (i : int) : term =
    let open Form in
    try List.at (direct_subterms t) i
    with Invalid_argument _ ->
      match t with
      | `F FPred _ | `E _ -> raise (InvalidSubExprPath [i])
      | `F _ -> raise (InvalidSubFormPath [i])
      
  let modify_direct_subterm (t : term) (u : term) (i : int) : term =
    let open Form in
    try
      List.modify_at i (fun _ -> u) (direct_subterms t) |>
      modify_direct_subterms t
    with Invalid_argument _ ->
      match t with
      | `F FPred _ | `E _ -> raise (InvalidSubExprPath [i])
      | `F _ -> raise (InvalidSubFormPath [i])


  let subterm (t : term) (p : int list) =
    try List.fold_left direct_subterm t p
    with InvalidSubFormPath _ -> raise (InvalidSubFormPath p)
       | InvalidSubExprPath _ -> raise (InvalidSubExprPath p)

  let subform (f : form) (p : int list) =
    match subterm (`F f) p with
    | `F f -> f
    | _ -> raise (InvalidSubFormPath p)

  let f_subexpr (f : form) (p : int list) =
    match subterm (`F f) p with
    | `E e -> e
    | _ -> raise (InvalidSubExprPath p)

  let e_subexpr (e : expr) (p : int list) =
    match subterm (`E e) p with
    | `E e -> e
    | _ -> raise (InvalidSubExprPath p)
    

  let rebuild_path i =
    let rec aux l = function
      | 0 -> 0::l
      | i -> aux (1::l) (i-1)
    in List.rev (aux [] i)

  let rebuild_pathd l i =
    if i+1 = l then [1] else
      
    let rec aux = function
      | 0 -> []
      | i -> 0::(aux (i-1))
    in
    if i = 0 then (aux (l-1)) else
      (aux (l - i - 1))@[1]


  let mk_ipath ?(ctxt : int = 0) ?(sub : int list = []) (root : int) =
    { root; ctxt; sub; }
    
  
  let item_ipath { root; ctxt; _ } =
    { root; ctxt; sub = [] }


  let path_of_ipath (p : ipath) =
    let pp_sub =
      Format.pp_print_list
        ~pp_sep:(fun fmt () -> Format.fprintf fmt "/")
        Format.pp_print_int
    in
    Format.asprintf "%d/%d:%a" p.root p.ctxt pp_sub p.sub

  let ipath_of_path (p : path) =
    let root, ctxt, sub =
      try
        Scanf.sscanf p "%d/%d:%s" (fun x1 x2 x3 -> (x1, x2, x3))
      with
      | Scanf.Scan_failure _
      | End_of_file ->
          raise (InvalidPath p) in

    if root < 0 || ctxt < 0 then
      raise (InvalidPath p);

    let sub =
      let sub = if sub = "" then [] else String.split_on_char '/' sub in

      try  List.map int_of_string sub
      with Failure _ -> raise (InvalidPath p)

    in

    if List.exists (fun x -> x < 0) sub then
      raise (InvalidPath p);

    { root; ctxt; sub; }

  let of_ipath (proof : Proof.proof) (p : ipath)
    : Proof.goal * item * (uid list * term)
  =
    let { root; ctxt; sub; } = p in

    let goal =
      try  Proof.byid proof (Handle.ofint root)
      with InvalidGoalId _ -> raise (InvalidPath (path_of_ipath p)) in

    let item, f_item =
      match ctxt with
      | ctxt when ctxt <= 0 ->
          let f = goal.Proof.g_goal in
          (`C f, f)

      | _ -> begin
          try
            let rp = Handle.ofint ctxt in
            let { Proof.h_form = hf; _ } as hyd =
              Proof.Hyps.byid goal.Proof.g_hyps rp
            in
            (`H (rp, hyd), hf)
          with InvalidHyphId _ -> raise (InvalidPath (path_of_ipath p))
        end
    in
    let target = subterm (`F f_item) sub in

    let goal = Proof.{ g_id = Handle.ofint root; g_pregoal = goal } in
    (goal, item, (sub, target))

  let is_sub_path (p : ipath) (sp : ipath) =
       p.root = sp.root
    && p.ctxt = sp.ctxt
    && List.is_prefix sp.sub p.sub

  (** [rewrite red res tgt targ] rewrites every occurrence of the reducible
      expression [red] in the subterm at path [tgt] into the residual
      expression [res]. It automatically shifts variables in [red] and [res]
      to avoid capture by binders in [tgt]. *)

  type pnode += TRewrite of expr * expr * ipath

  let rewrite (red : expr) (res : expr) (tgt : ipath) : tactic =
    let open Form in
    fun (proof, hd) ->
      
    let tgt = { tgt with root = Handle.toint hd } in
      
    let rec shift_then_doit red res (t : term) = function
      | [] -> rewrite red res t
      | i :: sub ->
          let u = direct_subterm t i in
          let u = shift_then_doit (shift_under t red) (shift_under t res) u sub in
          modify_direct_subterm t u i
    in

    let _, it, (sub, _) = of_ipath proof tgt in 
    let goal = Proof.byid proof hd in
    
    let subgoal = match it with
      | `H (src, { h_form = f; _ }) ->
          let new_hyp = shift_then_doit (`E red) (`E res) (`F f) sub |> form_of_term in
          [Some src, [new_hyp]], goal.Proof.g_goal

      | `C f ->
          let new_concl = shift_then_doit (`E red) (`E res) (`F f) sub |> form_of_term in
          [], new_concl
    in
    
    let pnode = TRewrite (red, res, tgt) in
    Proof.sprogress ~clear:true proof hd pnode [subgoal]
    

    let rewrite_in (red : expr) (res : expr) (tgts : ipath list) : tactic =
      List.fold_left
        (fun tac tgt -> then_tac tac (rewrite red res tgt))
        id_tac tgts


  (* -------------------------------------------------------------------- *)
  (** Polarities *)


  (** A subformula can either have a positive polarity [Pos], a negative polarity
      [Neg], or a superposition [Sup] of both.

      For example in the hypothesis (A ⇒ B) ∧ (C ⇔ D), A is positive, B is
      negative, and C and D can be either, depending on the way the user chooses
      to rewrite the equivalence. This coincides with the standard linear logic
      reading of equivalence as the additive conjunction of both directions of an
      implication. *)

  type pol = Pos | Neg | Sup


  (** [opp p] returns the opposite polarity of [p] *)

  let opp = function
    | Pos -> Neg
    | Neg -> Pos
    | Sup -> Sup


  (** [direct_subform_pol (p, f) i] returns the [i]th direct subformula of [f]
      together with its polarity, given that [f]'s polarity is [p] *)

  let direct_subform_pol (p, f : pol * form) (i : int) =
    match f with
    | FConn (c, fs) ->
      let subp =
        match c, i with
        | `Imp, 0 | `Not, 0 -> opp p
        | `Equiv, _ -> Sup
        | _, _ -> p
      in
      let subf =
        try List.at fs i
        with Invalid_argument _ -> raise (InvalidSubFormPath [i])
      in
      subp, subf
    | FBind (_, _, _, subf) ->
      p, subf
    | _ -> raise (InvalidSubFormPath [i])
  

  (** [subform_pol (p, f) sub] returns the subformula of [f] at path [sub] together
      with its polarity, given that [f]'s polarity is [p] *)

  let subform_pol (p, f) sub =
    try List.fold_left direct_subform_pol (p, f) sub
    with InvalidSubFormPath _ -> raise (InvalidSubFormPath sub)


  (** [neg_count f sub] counts the number of negations in [f] along path [sub] *)
  
  let neg_count (f : form) (sub : int list) : int =
    let aux (n, f) i =
      match f with
      | FConn (c, fs) ->
          let n =
            match c, i with
            | `Imp, 0 | `Not, 0 -> n+1
            | _ -> n
          in
          let subf =
            try List.at fs i
            with Invalid_argument _ -> raise (InvalidSubFormPath sub)
          in
          n, subf
      | FBind (_, _, _, subf) ->
          n, subf
      | _ ->
          raise (InvalidSubFormPath sub)
    in
    List.fold_left aux (0, f) sub |> fst


  (** [pol_of_item it] returns the polarity of the item [it] *)

  let pol_of_item = function
    | `H _ -> Neg
    | `C _ -> Pos


  (** [pol_of_ipath proof p] returns the polarity of the subformula
      at path [p] in [proof] *)

  let pol_of_ipath (proof : Proof.proof) (p : ipath) : pol =
    let _, item, (sub, _) = of_ipath proof p in
    let pol, form =
      match item with
      | `H (_, { h_form = f; _ }) -> Neg, f
      | `C f -> Pos, f
    in
    subform_pol (pol, form) sub |> fst


  (* -------------------------------------------------------------------- *)
  (** Linking *)
  

  type link = ipath * ipath
  type hyperlink = (ipath list) * (ipath list)
  
  let hyperlink_of_link : link -> hyperlink =
    fun (src, dst) -> [src], [dst]
  

  type pnode += TLink

  (** [link] is the equivalent of Proof by Pointing's [finger_tac], but using the
  interaction rules specific to subformula linking. *)

  let link (src, dst : link) (s_src, s_dst : Form.Subst.subst * Form.Subst.subst) : tactic =
    fun (proof, hd) ->

    assert (src.ctxt <> dst.ctxt);

    let s_src = Form.Subst.aslist s_src in
    let s_dst = Form.Subst.aslist s_dst in
    
    let goal = Proof.byid proof hd in
    let _, item_src, (sub_src, _) = of_ipath proof src in
    let _, item_dst, (sub_dst, _) = of_ipath proof dst in

    let rec pbp (goal, ogoals) tgt sub s tgt' sub' s' =

      let gen_subgoals target sub_goal sub_ogoals =
        let ogoals = Proof.sgprogress goal sub_ogoals in
        let goal =
          let goal = List.hd (Proof.sgprogress goal [sub_goal]) in
          match target with
          | `H (uid, hyp) ->
            { goal with g_hyps = Proof.Hyps.add goal.g_hyps uid hyp }
          | _ -> goal
        in
        (goal, ogoals)
      in

      let invertible (pol : pol) (f : form) : bool =
        match pol with
        (* Right invertible *)
        | Pos -> begin match f with
          | FConn (c, _) -> begin match c with
            | `And | `Imp | `Not -> true
            | _ -> false
            end
          | FBind (`Forall, _, _, _) -> true
          | _ -> false
          end
        (* Left invertible *)
        | Neg -> begin match f with
          | FConn (c, _) -> begin match c with
            | `And | `Or -> true
            | _ -> false
            end
          | FBind _ -> true
          | _ -> false
          end
        | Sup -> assert false
      in

      let right_inv_rules f i sub s tgt' sub' s' =
        let tgt, (goal, new_ogoals), s = begin match f, i+1 with

          (* And *)

          | FConn (`And, [f1; f2]), 1 ->
            let tgt = `C f1 in
            let subgoals = gen_subgoals tgt ([], f1) [[], f2] in
            tgt, subgoals, s

          | FConn (`And, [f1; f2]), 2 ->
            let tgt = `C f2 in
            let subgoals = gen_subgoals tgt ([], f2) [[], f1] in
            tgt, subgoals, s

          (* Imp *)

          | FConn (`Imp, [f1; f2]), 1 ->
            let tgt = `H (Handle.fresh (), Proof.mk_hyp f1) in
            let subgoals = gen_subgoals tgt ([], f2) [] in
            tgt, subgoals, s

          | FConn (`Imp, [f1; f2]), 2 ->
            let tgt = `C f2 in
            let subgoals = gen_subgoals tgt ([None, [f1]], f2) [] in
            tgt, subgoals, s

          (* Not *)

          | FConn (`Not, [f1]), 1 ->
            let tgt = `H (Handle.fresh (), Proof.mk_hyp f1) in
            let subgoals = gen_subgoals tgt ([], Form.f_false) [] in
            tgt, subgoals, s

          (* Forall *)

          | FBind (`Forall, x, ty, f), 1 ->
            begin match List.pop_assoc x s with
            | s, Sbound (EVar (z, _)) ->
              let f = Form.Subst.f_apply1 (x, 0) (EVar (z, 0)) f in
              let tgt = `C f in
              let goal, ogoals = gen_subgoals tgt ([], f) [] in
              let goal = { goal with g_env = Vars.push goal.g_env (z, ty, None) } in
              tgt, (goal, ogoals), s
            | _ -> raise TacticNotApplicable
            end
          
          | _ -> raise TacticNotApplicable

        end
        in pbp (goal, ogoals @ new_ogoals) tgt sub s tgt' sub' s'
      in

      let left_inv_rules f src i sub s tgt' sub' s' =
        let tgt, (goal, new_ogoals), s = begin match f, i+1 with

          (* And *)

          | FConn (`And, [f1; f2]), 1 ->
            let tgt = `H (Handle.fresh (), Proof.mk_hyp f1 ~src) in
            let subgoals =  gen_subgoals tgt ([Some src, [f2]], goal.g_goal) [] in
            tgt, subgoals, s

          | FConn (`And, [f1; f2]), 2 ->
            let tgt = `H (Handle.fresh (), Proof.mk_hyp f2 ~src) in
            let subgoals = gen_subgoals tgt ([Some src, [f1]], goal.g_goal) [] in
            tgt, subgoals, s

          (* Or *)

          | FConn (`Or, [f1; f2]), 1 ->
            let tgt = `H (Handle.fresh (), Proof.mk_hyp f1 ~src) in
            let subgoals = gen_subgoals tgt ([], goal.g_goal) [[Some src, [f2]], goal.g_goal] in
            tgt, subgoals, s

          | FConn (`Or, [f1; f2]), 2 ->
            let tgt = `H (Handle.fresh (), Proof.mk_hyp f2 ~src) in
            let subgoals = gen_subgoals tgt ([], goal.g_goal) [[Some src, [f1]], goal.g_goal] in
            tgt, subgoals, s

          (* Forall *)

          | FBind (`Forall, x, _, f), 1 ->
            let s, item = List.pop_assoc x s in
            let tgt, subgoals =
              match item with
              | Sbound t -> 
                let f = Form.Subst.f_apply1 (x, 0) t f in
                let tgt = `H (Handle.fresh (), Proof.mk_hyp f ~src) in
                tgt, gen_subgoals tgt ([], goal.g_goal) []
              | Sflex -> failwith "cannot go through uninstantiated quantifiers"
            in
            tgt, subgoals, s

          (* Exists *)

          | FBind (`Exist, x, ty, f), 1 ->
            begin match List.pop_assoc x s with
            | s, Sbound (EVar (z, _)) ->
              let f = Form.Subst.f_apply1 (x, 0) (EVar (z, 0)) f in
              let tgt = `H (Handle.fresh (), Proof.mk_hyp f ~src) in
              let goal, ogoals = gen_subgoals tgt ([], goal.g_goal) [] in
              let goal = { goal with g_env = Vars.push goal.g_env (z, ty, None) } in
              tgt, (goal, ogoals), s
            | _ -> raise TacticNotApplicable
            end
          
          | _ -> raise TacticNotApplicable

        end
        in pbp (goal, ogoals @ new_ogoals) tgt sub s tgt' sub' s'
      in

      match tgt, sub, s, tgt', sub', s' with

      (* Axiom *)

      | _, [], _, _, [], _ -> List.rev ogoals

      (* Right invertible rules *)

      | tgt', sub', s', `C f, i :: sub, s
        when invertible Pos f ->
        right_inv_rules f i sub s tgt' sub' s'

      | `C f, i :: sub, s, tgt', sub', s'
        when invertible Pos f ->
        right_inv_rules f i sub s tgt' sub' s'

      (* Left invertible rules *)

      | tgt', sub', s', `H (src, Proof.{ h_form = f; _ }), i :: sub, s
        when invertible Neg f ->
        left_inv_rules f src i sub s tgt' sub' s'

      | `H (src, Proof.{ h_form = f; _ }), i :: sub, s, tgt', sub', s'
        when invertible Neg f ->
        left_inv_rules f src i sub s tgt' sub' s'

      (* Right non-invertible rules *)

      | tgt', sub', s', `C f, i :: sub, s
      | `C f, i :: sub, s, tgt', sub', s' ->

        let tgt, (goal, new_ogoals), s = begin match f, i+1 with

          (* Or *)

          | FConn (`Or, [f1; _]), 1 ->
            let tgt = `C f1 in
            let subgoals = gen_subgoals tgt ([], f1) [] in
            tgt, subgoals, s

          | FConn (`Or, [_; f2]), 2 ->
            let tgt = `C f2 in
            let subgoals = gen_subgoals tgt ([], f2) [] in
            tgt, subgoals, s

          (* Exists *)

          | FBind (`Exist, x, _, f), 1 ->
            let s, item = List.pop_assoc x s in
            let tgt, subgoals =
              match item with
              | Sbound t -> 
                let f = Form.Subst.f_apply1 (x, 0) t f in
                let tgt = `C f in
                tgt, gen_subgoals tgt ([], f) []
              | Sflex -> failwith "cannot go through uninstantiated quantifiers"
            in
            tgt, subgoals, s
          
          | _ -> raise TacticNotApplicable

        end
        in pbp (goal, ogoals @ new_ogoals) tgt sub s tgt' sub' s'

      (* Left non-invertible rules *)

      | tgt', sub', s', `H (src, Proof.{ h_form = f; _ }), i :: sub, s
      | `H (src, Proof.{ h_form = f; _ }), i :: sub, s, tgt', sub', s' ->

        let tgt, (goal, new_ogoals), s = begin match tgt' with

          (* Hypothesis vs. Conclusion *)

          | `C _ -> begin match f, i+1 with

            (* Imp *)

            | FConn (`Imp, [f1; f2]), 2 ->
              let tgt = `H (Handle.fresh (), Proof.mk_hyp f2 ~src) in
              let subgoals = gen_subgoals tgt ([], goal.g_goal) [[], f1] in
              tgt, subgoals, s

            | _ -> raise TacticNotApplicable

            end

          (* Hypothesis vs. Hypothesis *)

          | `H _ -> begin match f, i+1 with

            (* Imp *)

            | FConn (`Imp, [f1; f2]), 1 ->
              let tgt = `C f1 in
              let subgoals = gen_subgoals tgt ([], f1) [[Some src, [f2]], goal.g_goal] in
              tgt, subgoals, s

            | FConn (`Imp, [f1; f2]), 2 ->
              let tgt = `H (Handle.fresh (), Proof.mk_hyp f2 ~src) in
              let subgoals = gen_subgoals tgt ([], goal.g_goal) [[], f1] in
              tgt, subgoals, s

            (* Not *)

            | FConn (`Not, [f1]), 1 ->
              let tgt = `C f1 in
              let subgoals = gen_subgoals tgt ([], f1) [] in
              tgt, subgoals, s
            
            | _ -> raise TacticNotApplicable

            end
          end
        in pbp (goal, ogoals @ new_ogoals) tgt sub s tgt' sub' s'
    in

    let subgoals = pbp (goal, []) item_src sub_src s_src item_dst sub_dst s_dst in
    Proof.xprogress proof hd TLink subgoals


  (** [elim_units f] eliminates all occurrences of units
      in formula [f] using algebraic unit laws. *)

  let rec elim_units : form -> form = function

    (* Absorbing elements *)

    | FConn (`And, [_; FFalse])
    | FConn (`And, [FFalse; _])
    | FConn (`Not, [FTrue])
    | FBind (`Exist, _, _, FFalse) ->
      Form.f_false

    | FConn (`Or, [_; FTrue])
    | FConn (`Or, [FTrue; _])
    | FConn (`Imp, [_; FTrue])
    | FConn (`Imp, [FFalse; _])
    | FConn (`Not, [FFalse])
    | FBind (`Forall, _, _, FTrue) ->
      Form.f_true

    (* Neutral elements *)

    | FConn (`And, [f; FTrue])
    | FConn (`And, [FTrue; f])
    | FConn (`Or, [f; FFalse])
    | FConn (`Or, [FFalse; f])
    | FConn (`Imp, [FTrue; f])
    | FConn (`Equiv, [FTrue; f])
    | FConn (`Equiv, [f; FTrue]) ->
      elim_units f
    
    | FTrue | FFalse | FPred _ as f -> f
    | FConn (c, fs) as f ->
      let fs' = List.map elim_units fs in
      if fs = fs' then f else elim_units (FConn (c, fs'))
    | FBind (b, x, ty, f1) as f ->
      let f1' = elim_units f1 in
      if f1 = f1' then f else elim_units (FBind (b, x, ty, f1'))
  
  
  (** [dlink] stands for _d_eep linking, and implements the deep interaction phase
      à la Chaudhuri for intuitionistic logic. *)
  
  let dlink (src, dst : link) (s_src, s_dst : Form.Subst.subst * Form.Subst.subst) : tactic =
    fun (proof, g_id) ->

    let open Form in
    let open Subst in
    let open Proof in
    
    let { g_pregoal = goal; _ }, item_src, (sub_src, t_src) = of_ipath proof src in
    let _, item_dst, (sub_dst, t_dst) = of_ipath proof dst in

    begin match t_src, t_dst with
      | `E _, `E _ -> raise TacticNotApplicable
      | _ -> ()
    end;

    (** [well_scoped e ctx] returns [true] if all variables in the expression
        [e] are bound either in the environment [goal.g_env], or by a
        quantifier in [ctx]. *)

    let well_scoped e ctx =
      e_vars e |> List.for_all begin fun x ->
        Vars.exists goal.g_env x ||
        c_is_bound x ctx
      end
    in

    let invertible (kind : [`Left | `Right | `Forward]) (f : form) : bool =
      match kind with
      (* Right invertible *)
      | `Right -> begin match f with
        | FConn (c, _) -> begin match c with
          | `Imp | `Not | `Equiv -> true
          | _ -> false
          end
        | FBind (`Forall, _, _, _) -> true
        | _ -> false
        end
      (* Left invertible *)
      | `Left -> begin match f with
        | FConn (c, _) -> begin match c with
          | `Or -> true
          | _ -> false
          end
        | FBind (`Exist, _, _, _) -> true
        | _ -> false
        end
      (* Forward invertible *)
      | `Forward -> begin match f with
        | FConn (c, _) -> begin match c with
          | `And -> true
          | _ -> false
          end
        | FBind (`Exist, _, _, _) -> true
        | _ -> false
        end
    in

    let rec backward (ctx : ctx)
      ((env1, s1 as es1), (env2, s2 as es2) as s : (LEnv.lenv * subst) * (LEnv.lenv * subst))
      (((l, lsub as h), (r, rsub as c)) as linkage : (term * int list) * (term * int list)) : form =
      
      match linkage with

      (** End rules *)

      | (_, []), (_, []) ->
        let f = begin match l, r with

          (* Bid *)
          | `F l, `F r when f_equal l r -> f_true
          | `F FPred (c1, ts1), `F FPred (c2, ts2) when c1 = c2 ->
            List.fold_left2
              (fun f t1 t2 -> f_and f (FPred ("_EQ", [t1; t2])))
              f_true ts1 ts2
            |> flatten_conjunctions
            |> fun l -> FConn (`And, l)
        
          (* Brel *)
          | `F l, `F r -> f_imp l r
          
          (* Ltrel *)
          | `E _, `F f
          (* Rtrel *)
          | `F f, `E _ -> f
          
          | _ -> raise TacticNotApplicable

          end
        in c_fill (`F f) (c_rev ctx) |> form_of_term
      
      | (`F FPred ("_EQ", [e1; e2]), [i]), (_, []) ->
        let red, res = begin match i with 
          (* L=₁ *)
          | 0 -> e1, e2
          (* L=₂ *)
          | 1 -> e2, e1
          | _ -> assert false
        end in
        let f = rewrite (`E red) (`E res) r in
        c_fill f (c_rev ctx) |> form_of_term
      
      (** Commuting rules *)

      | _ ->
        let switch_pol = ref false in
        let s = ref s in

        let (ictx : ictx),
            (linkage : (term * int list) * (term * int list)) =
          
          begin match linkage with
            
          (** Right rules *)
          
          (* Rfᵢ *)
          | _, (`E EFun (f, args), i :: sub) ->
            begin try
              let ei, es = List.pop_at i args in
              `E (CFun (f, es, i)), (h, (`E ei, sub))
            with Invalid_argument _ ->
              failwith "0-ary function"
            end

          (* RPᵢ *)
          | _, (`F FPred (p, args), i :: sub) ->
            begin try
              let ei, es = List.pop_at i args in
              `P (p, es, i), (h, (`E ei, sub))
            with Invalid_argument _ ->
              failwith "0-ary predicate"
            end

          (* R∧ *)
          | (`F l, _), (`F FConn (`And, fs), i :: sub)
            when not (invertible `Left l) || List.is_empty lsub ->
            begin try
              let fi, fs = List.pop_at i fs in
              `F (CConn (`And, fs, i)), (h, (`F fi, sub))
            with Not_found ->
              failwith "empty conjunction"
            end

          (* R∨ *)
          | (`F l, _), (`F FConn (`Or, fs), i :: sub)
            when not (invertible `Left l) || List.is_empty lsub ->
            begin try
              let fi, fs = List.pop_at i fs in
              `F (CConn (`Or, fs, i)), (h, (`F fi, sub))
            with Not_found ->
              failwith "empty disjunction"
            end

          (* R⇒₁ *)
          | _, (`F FConn (`Imp, [f1; f2]), 0 :: sub) ->
            switch_pol := true;
            `F (CConn (`Imp, [f2], 0)), (h, (`F f1, sub))

          (* R⇒₂ *)
          | _, (`F FConn (`Imp, [f1; f2]), 1 :: sub) ->
            `F (CConn (`Imp, [f1], 1)), (h, (`F f2, sub))

          (* R¬ *)
          | _, (`F FConn (`Not, [f1]), 0 :: sub) ->
            switch_pol := true;
            `F (CConn (`Not, [], 0)), (h, (`F f1, sub))

          | _, (`F FConn (`Equiv, [_; _]), _) ->
            failwith "DnD on positive equivalence currently unsupported"

          | (`F l, _), (`F FBind (`Exist, x, ty, f1), 0 :: sub)
            when (not (invertible `Left l) || List.is_empty lsub) &&
            match get_tag (x, LEnv.get_index (LEnv.enter env2 x) x) s2 with
            | Some Sbound e -> well_scoped e ctx 
            | Some Sflex -> true
            | None -> false
            ->
            let env2 = LEnv.enter env2 x in
            s := es1, (env2, s2);
            begin match get_tag (x, LEnv.get_index env2 x) s2 with
            (* R∃i *)
            | Some Sbound e ->
              let f1 = Subst.f_apply1 (x, 0) e f1 in
              `None, (h, (`F f1, sub))
            (* R∃s *)
            | Some Sflex ->
              let h = (`F (f_shift (x, 0) l), lsub) in
              `F (CBind (`Exist, x, ty)), (h, (`F f1, sub))
            | None -> assert false
            end

          (* R∀s *)
          | (`F l, _), (`F FBind (`Forall, x, ty, f1), 0 :: sub) ->
            let env2 = LEnv.enter env2 x in
            s := es1, (env2, s2);
            let h = `F (f_shift (x, 0) l), lsub in
            `F (CBind (`Forall, x, ty)), (h, (`F f1, sub))

          (** Left rules *)

          (* Lfᵢ *)
          | (`E EFun (f, args), i :: sub), _ ->
            begin try
              let ei, es = List.pop_at i args in
              `E (CFun (f, es, i)), ((`E ei, sub), c)
            with Invalid_argument _ ->
              failwith "0-ary function"
            end

          (* LPᵢ *)
          | (`F FPred (p, args), i :: sub), _ ->
            begin try
              let ei, es = List.pop_at i args in
              `P (p, es, i), ((`E ei, sub), c)
            with Invalid_argument _ ->
              failwith "0-ary predicate"
            end

          (* L∧ *)
          | (`F FConn (`And, fs), i :: sub), _ ->
            begin try
              `None, ((`F (List.at fs i), sub), c)
            with Invalid_argument _ ->
              failwith "empty conjunction"
            end

          (* L∨ *)
          | (`F FConn (`Or, fs), i :: sub), (`F r, _) ->
            begin try
              let fi, fs = List.pop_at i fs in
              let fs = List.map (fun fj -> f_imp fj r) fs in
              `F (CConn (`And, fs, i)), ((`F fi, sub), c)
            with Not_found ->
              failwith "empty disjunction"
            end
          
          (* L⇒₂ *)
          | (`F FConn (`Imp, [f1; f2]), 1 :: sub), (`F r, _)
            when not (invertible `Right r) || List.is_empty rsub ->
            `F (CConn (`And, [f1], 1)), ((`F f2, sub), c)

          (* L⇔₁ *)
          | (`F FConn (`Equiv, [f1; f2]), 0 :: sub), (`F r, _)
            when not (invertible `Right r) || List.is_empty rsub ->
            `F (CConn (`And, [f2], 0)), ((`F f1, sub), c)

          (* L⇔₂ *)
          | (`F FConn (`Equiv, [f1; f2]), 1 :: sub), (`F r, _)
            when not (invertible `Right r) || List.is_empty rsub ->
            `F (CConn (`And, [f1], 1)), ((`F f2, sub), c)
          
          (* L∃s *)
          | (`F FBind (`Exist, x, ty, f1), 0 :: sub), (`F r, _) ->
            let env1 = LEnv.enter env1 x in 
            s := (env1, s1), es2;
            let c = `F (f_shift (x, 0) r), rsub in
            `F (CBind (`Forall, x, ty)), ((`F f1, sub), c)

          | (`F FBind (`Forall, x, ty, f1), 0 :: sub), (`F r, _)
            when (not (invertible `Right r) || List.is_empty rsub) &&
            match get_tag (x, LEnv.get_index (LEnv.enter env1 x) x) s1 with
            | Some Sbound e -> well_scoped e ctx
            | Some Sflex -> true
            | None -> false
            ->
            let env1 = LEnv.enter env1 x in
            s := (env1, s1), es2;
            begin match get_tag (x, LEnv.get_index env1 x) s1 with
            (* L∀i *)
            | Some Sbound e ->
              let f1 = f_apply1 (x, 0) e f1 in
              `None, ((`F f1, sub), c)
            (* L∀s *)
            | Some Sflex ->
              let c = `F (f_shift (x, 0) r), rsub in
              `F (CBind (`Exist, x, ty)), ((`F f1, sub), c)
            | None -> assert false
            end
          
          | _ -> raise TacticNotApplicable
          end
        in
        let cont = if !switch_pol then forward else backward in
        let ctx = c_push ictx ctx in 
        cont ctx !s linkage
      

    and forward (ctx : ctx)
      (es1, (env2, s2 as es2) as s : (LEnv.lenv * subst) * (LEnv.lenv * subst))
      (((l, lsub as h), (r, _)) as linkage : (term * int list) * (term * int list)) : form =
      
      match linkage with

      (** End rules *)

      | (_, []), (_, []) ->

        let f = begin match l, r with
          (* Fid *)
          | `F l, `F r when f_equal l r -> l

          (* Frel *)
          | `F l, `F r -> f_and l r
          
          (* Ftrel *)
          | `E _, `F f
          | `F f, `E _ -> f
          
          | _ -> raise TacticNotApplicable
        end in
        c_fill (`F f) (c_rev ctx) |> form_of_term

      | (`F FPred ("_EQ", [e1; e2]), [i]), (_, []) ->
        let red, res = begin match i with 
          (* F=₁ *)
          | 0 -> e1, e2
          (* F=₂ *)
          | 1 -> e2, e1
          | _ -> assert false
        end in
        let f = rewrite (`E red) (`E res) r in
        c_fill f (c_rev ctx) |> form_of_term

      (** Commuting rules *)

      | _ ->
        let switch_pol = ref false in
        let s = ref s in

        let (ictx : ictx),
            (linkage : (term * int list) * (term * int list)) =
          
          begin match linkage with

          (* Ffᵢ *)
          | _, (`E EFun (f, args), i :: sub) ->
            begin try
              let ei, es = List.pop_at i args in
              `E (CFun (f, es, i)), (h, (`E ei, sub))
            with Invalid_argument _ ->
              failwith "0-ary function"
            end

          (* FPᵢ *)
          | _, (`F FPred (p, args), i :: sub) ->
            begin try
              let ei, es = List.pop_at i args in
              `P (p, es, i), (h, (`E ei, sub))
            with Invalid_argument _ ->
              failwith "0-ary predicate"
            end

          (* F∧ *)
          | _, (`F FConn (`And, fs), i :: sub) ->
            begin try
              let fi, fs = List.pop_at i fs in
              `F (CConn (`And, fs, i)), (h, (`F fi, sub))
            with Not_found ->
              failwith "empty conjunction"
            end

          (* F∨ *)
          | (`F l, _), (`F FConn (`Or, fs), i :: sub)
            when not (invertible `Forward l) || List.is_empty lsub ->
            begin try
              let fi, fs = List.pop_at i fs in
              `F (CConn (`Or, fs, i)), (h, (`F fi, sub))
            with Not_found ->
              failwith "empty disjunction"
            end

          (* F⇒₁ *)
          | (`F l, _), (`F FConn (`Imp, [f1; f2]), 0 :: sub)
            when not (invertible `Forward l) || List.is_empty lsub ->
            switch_pol := true;
            `F (CConn (`Imp, [f2], 0)), (h, (`F f1, sub))

          (* F⇒₂ *)
          | (`F l, _), (`F FConn (`Imp, [f1; f2]), 1 :: sub)
            when not (invertible `Forward l) || List.is_empty lsub ->
            `F (CConn (`Imp, [f1], 1)), (h, (`F f2, sub))

          (* F¬ *)
          | (`F l, _), (`F FConn (`Not, [f1]), 0 :: sub)
            when not (invertible `Forward l) || List.is_empty lsub ->
            switch_pol := true;
            `F (CConn (`Not, [], 0)), (h, (`F f1, sub))

          (* F⇔₁ *)
          | (`F l, _), (`F FConn (`Equiv, [f1; f2]), 0 :: sub)
            when not (invertible `Forward l) || List.is_empty lsub ->
            switch_pol := true;
            `F (CConn (`Imp, [f2], 0)), (h, (`F f1, sub))

          (* F⇔₂ *)
          | (`F l, _), (`F FConn (`Equiv, [f1; f2]), 1 :: sub)
            when not (invertible `Forward l) || List.is_empty lsub ->
            switch_pol := true;
            `F (CConn (`Imp, [f1], 0)), (h, (`F f2, sub))
          
          (* F∃s *)
          | (`F l, _), (`F FBind (`Exist, x, ty, f1), 0 :: sub) ->
            let env2 = LEnv.enter env2 x in
            s := es1, (env2, s2);
            let h = `F (f_shift (x, 0) l), lsub in
            `F (CBind (`Exist, x, ty)), (h, (`F f1, sub))
          
          | (`F l, _), (`F FBind (`Forall, x, ty, f1), 0 :: sub)
            when (not (invertible `Forward l) || List.is_empty lsub) &&
            match get_tag (x, LEnv.get_index (LEnv.enter env2 x) x) s2 with
            | Some Sbound e -> well_scoped e ctx
            | Some Sflex -> true
            | None -> false
            ->
            let env2 = LEnv.enter env2 x in
            s := es1, (env2, s2);
            begin match get_tag (x, LEnv.get_index env2 x) s2 with
            (* F∀i *)
            | Some Sbound e ->
              let f1 = Subst.f_apply1 (x, 0) e f1 in
              `None, (h, (`F f1, sub))
            (* F∀s *)
            | Some Sflex ->
              let h = `F (f_shift (x, 0) l), lsub in
              `F (CBind (`Forall, x, ty)), (h, (`F f1, sub))
            | None -> assert false
            end
            
          (* Fcomm *)
          | h, h' ->
            s := (es1, es2);
            `None, (h', h)
          end
        in
        let cont = if !switch_pol then backward else forward in
        let ctx = c_push ictx ctx in
        cont ctx !s linkage
    in

    let subgoal = match (item_src, sub_src, s_src), (item_dst, sub_dst, s_dst) with
      | (`H (hid, { h_form = h; _ }), subh, sh), (`C c, subc, sc)
      | (`C c, subc, sc), (`H (hid, { h_form = h; _ }), subh, sh) ->
        [[Some hid, []], backward (CForm []) ((LEnv.empty, sh), (LEnv.empty, sc)) ((`F h, subh), (`F c, subc)) |> elim_units]
      
      | (`H (hid, { h_form = h; _ }), subh, s), (`H (hid', { h_form = h'; _ }), subh', s') ->
        [[Some hid, []; Some hid', [forward (CForm []) ((LEnv.empty, s), (LEnv.empty, s')) ((`F h, subh), (`F h', subh')) |> elim_units]], goal.g_goal]
      
      | _ -> raise TacticNotApplicable
    in

    let pr = sprogress ~clear:false proof g_id TLink subgoal in
    List.fold_left (uncurry close_with_unit) pr (opened pr)

  
  (* -------------------------------------------------------------------- *)
  (** Logical actions *)

  type linkaction = [
    | `Nothing
    | `Both of linkaction * linkaction
    | `Subform of Form.Subst.subst * Form.Subst.subst
    | `Rewrite of expr * expr * ipath list
  ]

  let remove_nothing =
    let rec doit = function
      | [] -> []
      | a :: l -> match a with
        | `Nothing ->
            doit l
        | `Both (a, a') ->
            begin match doit [a; a'] with
            | [] -> doit l
            | [a] -> a :: doit l
            | [a; a'] -> `Both (a, a') :: doit l
            | _ -> assert false
            end
        | _ ->
            a :: doit l
    in doit
          
  let string_of_linkaction proof =
    let rec doit = function
      | `Nothing -> "⊥"
      | `Both (a, a') -> Printf.sprintf "(%s, %s)" (doit a) (doit a')
      | `Subform _ -> "SFL"
      | `Rewrite (red, res, tgts) ->
          Printf.sprintf "%s[%s ~> %s]"
            (List.to_string ~sep:", " ~left:"{" ~right:"}"
              (fun p -> let _, _, (_, t) = of_ipath proof p in Form.tostring t)
             tgts)
            red res
    in doit

  type action = Handle.t * [
    | `Elim      of Handle.t
    | `Intro     of int
    | `Forward   of Handle.t * Handle.t * (int list) * Form.Subst.subst 
    | `DisjDrop  of Handle.t * form list
    | `ConjDrop  of Handle.t
    | `Hyperlink of hyperlink * linkaction list
  ]
  
  
  (* -------------------------------------------------------------------- *)
  (** (Hyper)link search (for highlighting) *)

  
  (** [t_subs f] returns all the paths leading to a subterm in [t]. *)
  
  let t_subs (t : term) : (int list) list =

    let rec aux sub = function
      | `E EFun (_, es)
      | `F FPred (_, es) ->
        es |> List.mapi (fun i e ->
                let sub = sub @ [i] in
                sub :: aux sub (`E e))
           |> List.concat
      | `F FConn (_, fs) ->
        fs |> List.mapi (fun i f ->
                let sub = sub @ [i] in
                sub :: aux sub (`F f))
           |> List.concat
      | `F FBind (_, _, _, f) ->
        let sub = sub @ [0] in
        sub :: aux sub (`F f)
      | _ -> []

    in [] :: aux [] t


  (** [f_subs f] returns all the paths leading to a subformula in [f]. *)

  let f_subs (f : form) : (int list) list =

    let rec aux sub = function
      | FConn (_, fs) ->
        fs |> List.mapi (fun i f ->
                let sub = sub @ [i] in
                sub :: aux sub f)
           |> List.concat
      | FBind (_, _, _, f) ->
        let sub = sub @ [0] in
        sub :: aux sub f
      | _ -> []

    in [] :: (aux [] f)


  (** [e_subs f] returns all the paths leading to a subexpression in [f]. *)

  let e_subs (f : form) : (int list) list =

    let rec f_aux sub = function
      | FPred (_, es) ->
        es |> List.mapi (fun i e ->
                let sub = sub @ [i] in
                sub :: e_aux sub e)
           |> List.concat
      | FConn (_, fs) ->
        fs |> List.mapi (fun i f -> f_aux (sub @ [i]) f)
           |> List.concat
      | FBind (_, _, _, f) ->
        f_aux (sub @ [0]) f
      | _ -> []

    and e_aux sub = function
      | EVar _ -> []
      | EFun (_, es) ->
        es |> List.mapi (fun i e ->
                let sub = sub @ [i] in
                sub :: e_aux sub e)
           |> List.concat

    in f_aux [] f

  
  (** The type of hyperlink predicates [hlpred] captures functions which
      map a hyperlink in a proof to a list of possible link actions.

      One can emulate a traditional boolean predicate by returning the singleton
      [`Nothing] to indicate membership, or the empty list to indicate absence
      thereof. *)

  type lpred = Proof.proof -> link -> linkaction list
  type hlpred = Proof.proof -> hyperlink -> linkaction list
  
  let hlpred_of_lpred : lpred -> hlpred =
    fun p pr -> function
      | [src], [dst] -> p pr (src, dst)
      | _ -> []

  
  (** [hlpred_mult lps] returns a hyperlink predicate that denotes the cartesian
      product of the actions denoted by the hyperlink predicates in [lps]. *)

  let hlpred_mult : hlpred list -> hlpred =
    let mult : hlpred -> hlpred -> hlpred =
      fun p1 p2 -> fun pr lnk ->
        List.cartesian_product (p1 pr lnk) (p2 pr lnk) |>
        List.map (fun (a1, a2) -> `Both (a1, a2))
    in
    List.fold_left mult (fun _ _ -> [`Nothing])


  (** [hlpred_add lps] returns a hyperlink predicate that denotes the disjoint
      union of the actions denoted by the hyperlink predicates in [lps]. *)

  let hlpred_add : hlpred list -> hlpred =
    fun ps -> fun pr lnk ->
      List.map (fun p -> p pr lnk) ps |> 
      List.concat


  (** [search_linkactions hlp proof (src, dst)] returns all links between
      subterms of [src] and [dst] in [proof] that can interact according to
      the hyperlink predicate [hlp], together with the lists of possible link
      actions determined by the predicate.

      If [fixed_srcs] (resp. [fixed_dsts]) is set, the function returns only
      hyperlinks with sources [fixed_srcs] (resp. destinations [fixed_dsts]),
      and whose destinations (resp. sources) are subterms of [dst] (resp.
      [src]). *)
  
  let search_linkactions
    ?(fixed_srcs : ipath list option) ?(fixed_dsts : ipath list option)
    (hlp : hlpred) proof (src, dst : link) :
    (hyperlink * linkaction list) list
  =
    let subpath p sub = { root = p.root; ctxt = p.ctxt; sub = p.sub @ sub } in
    
    let query_actions lnk =
      match hlp proof lnk with
      | _ :: _ as actions -> [lnk, actions]
      | [] -> []
    in

    let open Monad.List in

    match fixed_srcs, fixed_dsts with
    | Some srcs, Some dsts ->
        query_actions (srcs, dsts)
    
    | Some srcs, None ->
        let _, _, (_, t_dst) = of_ipath proof dst in
        t_subs t_dst >>= fun sub_dst ->
        query_actions (srcs, [subpath dst sub_dst])

    | None, Some dsts ->
        let _, _, (_, t_src) = of_ipath proof src in
        t_subs t_src >>= fun sub_src ->
        query_actions ([subpath src sub_src], dsts)

    | None, None ->
        let _, _, (_, t_src) = of_ipath proof src in
        let _, _, (_, t_dst) = of_ipath proof dst in
        t_subs t_src >>= fun sub_src ->
        t_subs t_dst >>= fun sub_dst ->
        query_actions ([subpath src sub_src], [subpath dst sub_dst])


  (** [wf_subform_link proof (src, dst)] checks if [src] and [dst] lead to
      unifiable subformulas of opposite polarities in the focused goal of
      [proof], and returns the associated substitutions if they do inside a
      [`Subform] link action. *)

  let wf_subform_link : lpred =
    let open Form in

    (* Auxiliary definitions *)

    let module Deps = struct
      include Graph.Persistent.Digraph.Concrete(Name)

      let subst (deps : t) (s : Subst.subst) : t =
        (* For each item [x := e] in the substitution *)
        Subst.fold begin fun deps (x, tag) ->
          let fvs = match tag with
            | Sbound e -> e_vars e
            | Sflex -> []
          in
          (* For each variable [y] depending on [x] *)
          try fold_succ begin fun y deps ->
            (* For each variable [z] occurring in [e] *)
            List.fold_left begin fun deps (z, _) ->
                (* Add an edge stating that [y] depends on [z] *)
                add_edge deps z y
              end deps fvs
            end deps x deps
          with Invalid_argument _ -> deps
        end deps s
    end in
    let module TraverseDeps = Graph.Traverse.Dfs(Deps) in
    let acyclic = not <<| TraverseDeps.has_cycle in

    let module Env = struct
      (* While traversing formulas in search for targets to unify, we need to
         record and update multiple informations handling the first-order content
         of the proof. We do so with a tuple of the form
           
           [(deps, rnm, env, s)]
           
         where:

         - [deps] is a directed graph recording the dependency relation between
           existential and eigenvariables, in the same spirit of the dependency
           relation of expansion trees.

         - [rnm] is an association list, where each item [(z, x)] maps a fresh name
           [z] to the variable [x] it renames. Indeed, to avoid name clashes between
           bound variables of [f1] and [f2] during unification, we give them temporary
           fresh names, which are reverted to the original names with [rnm] when
           producing the final substitution for each formula.
          
         - [env] is (a copy of) the goal's environment, used to compute fresh
           names for eigenvariables that will be introduced by the [link] tactic.
          
         - [s] is the substitution that will be fed to unification, in which we
           record existential variables in [Sflex] entries, as well as the fresh
           eigenvariables in [Sbound] entries together with their original names.
      *)
      type t = Deps.t * (name * name) list * env * Subst.subst
    end in
    let module State = Monad.State(Env) in

    let traverse (p, f) i : (pol * form) State.t =
      let open State in
      match p, f with

      | Pos, FBind (`Forall, x, ty, f)
      | Neg, FBind (`Exist, x, ty, f) ->

        get >>= fun (deps, rnm, env, s) ->
        let y, env = Vars.bind env (x, ty) in
        let exs = Subst.fold
          (fun acc (x, t) -> if t = Sflex then x :: acc else acc)
          [] s
        in
        let deps = List.fold_left
          (fun deps x -> Deps.add_edge deps x y)
          deps exs
        in
        let z = EVars.fresh () in
        let rnm = (z, x) :: rnm in
        let s = Subst.push z (Sbound (EVar (y, 0))) s in
        put (deps, rnm, env, s) >>= fun _ ->
        return (p, Form.Subst.f_apply1 (x, 0) (EVar (y, 0)) f)

      | Neg, FBind (`Forall, x, _, f)
      | Pos, FBind (`Exist, x, _, f) ->

        get >>= fun (deps, rnm, env, s) ->
        let z = EVars.fresh () in
        let rnm = (z, x) :: rnm in
        let s = Subst.push z Sflex s in
        put (deps, rnm, env, s) >>= fun _ ->
        return (p, Form.Subst.f_apply1 (x, 0) (EVar (z, 0)) f)

      | _ -> return (direct_subform_pol (p, f) i)
    in

    let traverse = State.fold traverse in

    (* Body *)

    fun proof (src, dst) ->

    let Proof.{ g_pregoal; _ }, item_src, (sub_src, t_src) = of_ipath proof src in
    let _, item_dst, (sub_dst, t_dst) = of_ipath proof dst in

    match t_src, t_dst with
    | `F _, `F _ ->

      let f1 = form_of_item item_src in
      let f2 = form_of_item item_dst in

      let p1 = pol_of_item item_src in
      let p2 = pol_of_item item_dst in

      let sub1 = sub_src in
      let sub2 = sub_dst in

      let deps, sp1, sf1, rnm1, s1, sp2, sf2, rnm2, s2 =
        let open State in
        run begin
          traverse (p1, f1) sub1 >>= fun (sp1, sf1) ->
          get >>= fun (deps, rnm1, env, s1) ->
          put (deps, [], env, Subst.empty) >>= fun _ ->

          traverse (p2, f2) sub2 >>= fun (sp2, sf2) ->
          get >>= fun (deps, rnm2, _, s2) ->

          return (deps, sp1, sf1, rnm1, s1, sp2, sf2, rnm2, s2)
        end
        (Deps.empty, [], Proof.(g_pregoal.g_env), Subst.empty)
      in

      let s1 = Subst.aslist s1 in
      let s2 = Subst.aslist s2 in
      
      let open Monad.List in

      begin match sp1, sp2 with

      | Pos, Neg | Neg, Pos | Sup, _ | _, Sup ->

        begin match f_unify LEnv.empty (Subst.oflist (s1 @ s2)) [sf1, sf2] with

        | Some s when acyclic (Deps.subst deps s) ->

          let s1, s2 = List.split_at (List.length s1) (Subst.aslist s) in

          let rename rnm1 rnm2 =
            List.map begin fun (x, tag) ->
              let get_name x rnm = Option.default x (List.assoc_opt x rnm) in
              let x = get_name x rnm1 in
              let tag =
                let rec rename = function
                  | EVar (x, i) -> EVar (get_name x rnm2, i)
                  | EFun (f, es) -> EFun (f, List.map rename es)
                in match tag with
                | Sbound e -> Sbound (rename e)
                | _ -> tag
              in x, tag
            end
          in

          let s1 = s1 |> rename rnm1 rnm2 |> List.rev |> Subst.oflist in
          let s2 = s2 |> rename rnm2 rnm1 |> List.rev |> Subst.oflist in

          return (`Subform (s1, s2))

        | _ -> []
        end
      | _ -> []
      end
    | _ -> []
    
  
  (** [intuitionistic_link lnk] checks if [lnk] is an intuitionistic link,
      and returns a [`Nothing] link action if so. *)
  
  let intuitionistic_link : lpred =
    fun proof (src, dst) ->

    let neg_count (p : ipath) =
      let _, it, (sub, _) = of_ipath proof p in
      let f = form_of_item it in
      let n = neg_count f sub in
      match it with
      | `C _ -> n
      | `H _ -> n+1
    in
    
    try
      match neg_count src, neg_count dst with
      | m, n when m > 0 && n > 0
               || m = 0 && n <= 1
               || m <= 1 && n = 0 -> [`Nothing]
      | _ -> []
    with InvalidSubFormPath _ -> []
  

  (** [rewrite_link lnk] checks if [lnk] is a rewrite hyperlink. That is, one
      end of the link is the left or right-hand side expression [e] of an
      equality hypothesis, and the other end a non-empty set of arbitrary
      subterms where all occurrences of [e] are to be rewritten.

      If the check succeeds, it returns a [`Rewrite (red, res, tgts)] link
      action, where [red] and [res] are respectively the reduced ([e]) and
      residual expressions, and [tgts] are the targeted subterms. *)
  
  let rewrite_link : hlpred =
    fun proof lnk ->
    
    let rewrite_data (p : ipath) =
      if p.ctxt > 0 then
        let _, it, _ = of_ipath proof p in
        match p.sub, form_of_item it with
        | [0], FPred ("_EQ", [red; res])
        | [1], FPred ("_EQ", [res; red]) -> Some (red, res)
        | _ -> None
      else None
    in
    
    try
      match lnk, pair_map (List.hd |>> rewrite_data) lnk with
      (* If it is a simple link where both ends are sides of equalities,
         disambiguate by rewriting into the destination *)
      | ([_], [dst]), (Some (red, res), Some _) ->
          [`Rewrite (red, res, [dst])]

      | (_, tgts), (Some (red, res), _)
      | (tgts, _), (_, Some (red, res)) ->
          [`Rewrite (red, res, tgts)]
          
      | _ -> []
    (* Empty link end *)
    with Failure _ -> []
    
      
  (* -------------------------------------------------------------------- *)
  (** Graphical actions *)

  type asource =
    { kind : asource_kind; selection : selection; }

  and asource_kind = [
    | `Click of ipath
    | `DnD   of adnd
  ]

  and adnd = {
    source      : ipath;
    destination : ipath option;
  }

  and selection = ipath list

  type osource = [
    | `Click of ipath
    | `DnD   of link
  ]

  (** [dnd_actions dnd] computes all possible proof actions associated with the
      DnD action [dnd], and packages them as an array of output actions as
      specified in the JS API.

      More specifically, it will try to query actions for hyperlinks whose
      sources (resp. destinations) are those of [selection] occuring in
      [dnd.source] (resp. elsewhere), and which yield at least one action.

      If the source (resp. destination) selection is empty, it will search for
      hyperlinks with only one source (resp. destination) which is a subterm of
      [dnd.source] (resp. [dnd.destination]). If [dnd.destination] is [None], it
      will search for destinations everywhere in the current goal.
 *)

  let dnd_actions ((dnd, selection) : adnd * selection) (proof : Proof.proof) =
    let Proof.{ g_id; g_pregoal }, _, _ = of_ipath proof dnd.source in

    let srcsel : selection =
      List.filter (is_sub_path dnd.source) selection in

    let dstsel : selection =
      List.remove_if (fun p -> p.ctxt = dnd.source.ctxt) selection in

    let hlp = hlpred_add [
      hlpred_mult (List.map hlpred_of_lpred [wf_subform_link; intuitionistic_link]);
      rewrite_link
    ] in
    
    let dummy_path = mk_ipath 0 in

    let srcs, fixed_srcs = begin match srcsel with
      | [] -> [dnd.source], None
      | srcs -> [dummy_path], Some srcs
      end in

    let dsts, fixed_dsts = begin match dstsel with
      | [] ->
          let dsts = begin match dnd.destination with
            | None ->
                let src = dnd.source in
                (* Get the list of hypotheses handles *)
                Proof.Hyps.ids g_pregoal.Proof.g_hyps |>
                (* Create a list of paths to each hypothesis *)
                List.map begin fun id ->
                  mk_ipath (Handle.toint g_id) ~ctxt:(Handle.toint id)
                end |>
                (* Add a path to the conclusion *)
                fun hyps -> mk_ipath (Handle.toint g_id) :: hyps |>
                (* Remove the source from the list of paths *)
                fun dsts -> List.remove dsts src
                
            | Some dst ->
                [dst]
            end in
          dsts, None

      | dsts ->
          [dummy_path], Some dsts
      end in

    let open Monad.List in

    srcs >>= fun src ->
    dsts >>= fun dst ->

    let linkactions = search_linkactions hlp proof
      ?fixed_srcs ?fixed_dsts (src, dst) in

    linkactions >>= fun ((srcs, dsts) as lnk, actions) ->
    let actions = remove_nothing actions in
    srcs >>= fun src ->
    dsts >>= fun dst ->
    return ("Hyperlink", srcs @ dsts, `DnD (src, dst), (g_id, `Hyperlink (lnk, actions)))

      
  let actions (proof : Proof.proof) (p : asource)
      : (string * ipath list * osource * action) list
  =
    match p.kind with
      | `Click path -> begin
          let Proof.{ g_id = hd; g_pregoal = _goal}, item, (_fs, _subf) =
            of_ipath proof path
          in
          match item with
          | `C _ -> begin
              let iv = ivariants (proof, hd) in
              let bv = List.length iv <= 1 in
              List.mapi
                (fun i x ->
                  let hg = mk_ipath (Handle.toint hd) 
                    ~sub:(if bv 
                          then [] 
                          else rebuild_pathd (List.length iv) i)
                  in
                  (x, [hg], `Click hg, (hd, `Intro i)))
                iv
            end 

          | `H (rp, _) ->
            let hg = mk_ipath (Handle.toint hd) ~ctxt:(Handle.toint rp) in
            ["Elim", [hg], `Click hg, (hd, `Elim rp)]
        end

      | `DnD dnd ->
        dnd_actions (dnd, p.selection) proof

  
  let apply (proof : Proof.proof) ((hd, a) : action) =
    match a with
    | `Intro variant ->
        intro ~variant:(variant, None) (proof, hd)
    | `Elim subhd ->
        elim subhd (proof, hd)
    | `DisjDrop (subhd, fl) ->
        or_drop subhd (proof, hd) (List.map (fun x -> [Some hd, []],x) fl)
    | `ConjDrop subhd ->
        and_drop subhd (proof, hd)
    | `Forward (src, dst, p, s) ->
        forward (src, dst, p, s) (proof, hd)
    | `Hyperlink (lnk, actions) ->
        match lnk, actions with
        | ([src], [dst]), [`Subform substs] ->
            dlink (src, dst) substs (proof, hd)
        | _, [`Rewrite (red, res, tgts)] ->
            rewrite_in red res tgts (proof, hd)
        | _, _ :: _ :: _ -> failwith "Cannot handle multiple link actions yet"
        | _, _ -> raise TacticNotApplicable
end
