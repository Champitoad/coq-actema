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
  type path   = string
  type ipath  = { root : int; ctxt : int; sub : int list; }
  type gpath  = [`S of path | `P of ipath]
  type pol = Pos | Neg

  val cut        : Fo.form -> tactic
  val add_local  : string * Fo.type_ * Fo.expr -> tactic
  val generalize : Handle.t -> tactic
  val move       : Handle.t -> Handle.t option -> tactic
  val intro      : ?variant:(int * (expr * type_) option) -> tactic
  val elim       : ?clear:bool -> Handle.t -> tactic
  val ivariants  : targ -> string list
  val forward    : (Handle.t * Handle.t * int list * Fo.subst) -> tactic

  type asource = [
    | `Click of gpath
    | `DnD   of adnd
  ]

  and adnd = { source : gpath; destination : gpath option; }

  type osource = [
    | `Click of ipath
    | `DnD   of ipath * ipath
  ]

  val path_of_ipath : ipath -> path

  type action = Handle.t * [
    | `Elim    of Handle.t
    | `Intro   of int
    | `Forward of Handle.t * Handle.t * (int list) * Fo.subst 
    | `DisjDrop of Handle.t * form list
    | `ConjDrop of Handle.t
    | `Link of ipath * Fo.subst * ipath * Fo.subst
  ]

  exception InvalidPath

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
  type path   = string
  type ipath  = { root : int; ctxt : int; sub : int list; }
  type gpath  = [`S of path | `P of ipath]
  type pol    = Pos | Neg

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
    in fun f -> doit 0 [] [] f

  let prune_premisses_fad =
    let rec doit i acc s = function
      | FConn (`Imp, [f1; f2]) -> doit i ((s, f1) :: acc) s f2
      | FBind (`Forall, x, _, f) -> doit (i+1) acc ((x, Sflex)::s) f
      | f -> (List.rev acc, f, s)
    in fun f -> doit 0 [] [] f
	
  let prune_premisses_ex =
    let rec doit i acc s = function
      | FBind (`Exist, x, _, f) -> doit (i+1) acc ((x, Sflex)::s) f
      | f -> (List.rev acc, f, s)
    in fun f -> doit 0 [] [] f
	
  let rec remove_form f = function
      | [] -> raise TacticNotApplicable
      | g::l when Form.f_equal g f -> l
      | g::l -> g::(remove_form f l)

  type pnode += TIntro of (int * (expr * type_) option)

  let intro ?(variant = (0, None)) ((pr, id) : targ) =
    let pterm = TIntro variant in

    match variant, (Proof.byid pr id).g_goal with
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
        let goal = { goal with
          g_env  = Vars.push goal.g_env (x, xty, None);
          g_goal = body;
        }
        in Proof.xprogress pr id pterm [goal]

    | (0, Some (e, ety)), FBind (`Exist, x, xty, body) -> begin
        let goal = Proof.byid pr id in

        Fo.Form.erecheck goal.g_env ety e;
        if not (Form.t_equal xty ety) then
          raise TacticNotApplicable;
        let goal = Fo.Form.subst1 (x, 0) e body in
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

    (*
  let elim ?clear (h : Handle.t) ((pr, id) : targ) =
    let gl = Proof.byid pr id in
    let hy = (Proof.Hyps.byid gl.g_hyps h).h_form in

    if Form.f_equal hy gl.g_goal
    then  Proof.progress pr id (TElim id) [] 
    else

    try
(      let pre, hy, s = prune_premisses_fa hy in


      
      match Form.f_matchl s [(hy, gl.g_goal)] with
	| Some s when Form.s_complete s ->  
	    let pres = List.map 
			 (fun x -> [Some h, []], (Form.iter_subst s x))
			 pre
	      in 	    Proof.sprogress pr id (TElim id) pres
			      
	| Some _ -> failwith "incomplete match"
	| _ ->
	      let subs = List.map (fun (_, f) -> [Some h, []], f) pre in
	      ( match hy with
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

		  | _ -> raise TacticNotApplicable)
)
      with
	| TacticNotApplicable ->
      let _ , goal, s = prune_premisses_ex gl.g_goal in
      match Form.f_matchl s [(goal, hy)] with
	| Some s when Form.s_complete s ->
	    Proof.sprogress pr id (TElim id) []
	| Some _ -> failwith "incomplete ex match"
	| None ->
	    match goal with
	      | FConn (`Or , _) ->
		  let gll = Form.flatten_disjunctions goal in
		  let rec aux = function
		    | [] -> false
		    | g::l ->
			(  match Form.f_matchl s [(g, hy)] with
			     | Some s when Form.s_complete s -> true
			     | _ -> aux l
			)
		  in 
		  if aux gll 
		  then Proof.sprogress pr id (TElim id) []
		  else raise TacticNotApplicable
	      | _ -> raise TacticNotApplicable

*)


  let core_elim ?clear (h : Handle.t) ((pr, id) : targ) =
    let result = ref ([])  in 
    let gl = Proof.byid pr id in
    let hyp = (Proof.Hyps.byid gl.g_hyps h).h_form in

    if Form.f_equal hyp gl.g_goal
    then  result := [(TElim id), [] ] 
    else ();

    let pre, hy, s = prune_premisses_fa hyp in
    begin match Form.f_unify Env.empty s [(hy, gl.g_goal)] with
    | Some s when Form.s_complete s ->  
        let pres = List.map
        (fun x-> [Some h, []], (Form.iter_subst s x) ) pre in
        result :=  ((TElim id), pres)::!result
    | Some _ -> () (* "incomplete match" *)
    | _ -> ();
    end;
    let subs = List.map (fun (_, f) -> [Some h, []], f) pre in
    begin match hy with
    | FConn (`And, [f1; f2]) ->
        result := ((TElim id), subs@ [[Some h, [f1; f2]], gl.g_goal]) :: !result
    (* clear *) 
    | FConn (`Or, [f1; f2]) ->
        result := ((TElim id), 
                   subs @ [[Some h, [f1]], gl.g_goal;
                           [Some h, [f2]], gl.g_goal]) :: !result
    | FConn (`Equiv, [f1; f2]) ->
        result := ((TElim id),
                   (subs @ [[Some h, [Form.f_imp f1 f2;
                                      Form.f_imp f2 f1]], gl.g_goal])) :: !result
    | FConn (`Not, [f]) ->
        result := ((TElim id), 
                  (subs @ [[Some h, []], f])) :: !result
    | FFalse -> result := ((TElim id), subs) :: !result
    | _ -> ()
    end;
    let _ , goal, s = prune_premisses_ex gl.g_goal in
    let pre, hy = prune_premisses hyp in
    let pre = List.map (fun x -> [(Some h), []],x) pre in
    begin match Form.f_unify Env.empty s [(hy, goal)] with
    | Some s when Form.s_complete s ->
        result := ((TElim id), pre) :: !result
    | Some _ -> () (* failwith "incomplete ex match" *)
    | None ->
        match goal with
        | FConn (`Or , _) ->
          let gll = Form.flatten_disjunctions goal in
          let rec aux = function
            | [] -> false
            | g::l -> begin match Form.f_unify Env.empty s [(hyp, g)] with
                | Some s when Form.s_complete s -> true
                | _ -> aux l
              end
          in 
          if aux gll 
          then result := ((TElim id), []) :: !result
          else ()
        | _ -> ()
    end;
    !result


let perform l pr id =
  match l with
    | (t, l)::_ -> Proof.sprogress pr id t l
    | _ -> raise TacticNotApplicable
  
let elim ?clear (h : Handle.t) ((pr, id) : targ) =
  perform (core_elim ?clear h (pr, id)) pr id
	

      

	    
  let ivariants ((pr, id) : targ) =
    match (Proof.byid pr id).g_goal with
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
    let gl  = Proof.byid pr id in
    let src = (Proof.Hyps.byid gl.g_hyps hsrc).h_form in
    let dst = (Proof.Hyps.byid gl.g_hyps hdst).h_form in

    (* Here we eventually should have the call to the proof tactics *)
    let rec build_dest = function
      | ((FBind (`Forall, x, ty, f)), 0::p, ((y, Sflex)::s)) ->
          FBind (`Forall, x, ty, build_dest (f, p, s))
      | ((FBind (`Forall, x, ty, f)), 0::p, ((y, (Sbound e))::s)) ->
          build_dest ((Form.f_subst (x, 0) e f), p, s)
      | (FConn (`Imp, [f1; f2]), (0::_), s) ->
          Form.iter_subst s (List.length s, f2)
      | (FConn (`Imp, [f1; f2]), (1::p), s) ->
          FConn(`Imp, [Form.iter_subst s (List.length s, f1);
          build_dest (f2, p, s)])
      | _ -> failwith "cannot build forward"
    in
    let nf = build_dest (dst, p, s) in

    [ (TForward (hsrc, hdst)), [[Some hdst, [nf]], gl.g_goal] ]

  let forward (hsrc, hdst, p, s) ((pr, id) : targ) =
    perform (core_forward (hsrc, hdst, p, s) (pr, id)) pr id 

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

  type action = Handle.t * [
    | `Elim     of Handle.t
    | `Intro    of int
    | `Forward  of Handle.t * Handle.t * (int list) * Fo.subst 
    | `DisjDrop of Handle.t * form list
    | `ConjDrop of Handle.t
    | `Link     of ipath * Fo.subst * ipath * Fo.subst
  ]

  exception InvalidPath
  exception InvalidFormPath

  let rec subform (f : form) (p : int list) =
    match p with [] -> f | i :: subp ->

    match f with
    | FConn (_, fs) ->
        let subf =
          try  List.nth fs i
          with Failure _ -> raise InvalidFormPath
        in subform subf subp
    
    | FBind (_, _, _, f) -> subform f subp

    | _ -> raise InvalidFormPath

  let mk_ipath ?(ctxt : int = 0) ?(sub : int list = []) (root : int) =
    { root; ctxt; sub; }

  let ipath_strip (p : ipath) =
    { p with sub = [] }

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
          raise InvalidPath in

    if root < 0 || ctxt < 0 then
      raise InvalidPath;

    let sub =
      let sub = if sub = "" then [] else String.split_on_char '/' sub in

      try  List.map int_of_string sub
      with Failure _ -> raise InvalidPath

    in

    if List.exists (fun x -> x < 0) sub then
      raise InvalidPath;

    { root; ctxt; sub; }

  let of_ipath (proof : Proof.proof) (p : ipath)
    : Proof.goal * [> `C of form | `H of Handle.t * Proof.hyp ] * (uid list * form)
  =
    let { root; ctxt; sub; } = p in

    let goal =
      try  Proof.byid proof (Handle.ofint root)
      with InvalidGoalId _ -> raise InvalidPath in

    let target, subf =
      try
        match ctxt with
        | ctxt when ctxt <= 0 ->
            (`C goal.Proof.g_goal, subform goal.Proof.g_goal sub)
  
        | _ -> begin
            try
              let rp = Handle.ofint ctxt in
              let { Proof.h_form = hf; _ } as hyd =
                Proof.Hyps.byid goal.Proof.g_hyps rp in
              (`H (rp, hyd), subform hf sub)
            with InvalidHyphId _ -> raise InvalidPath
          end

      with InvalidFormPath -> raise InvalidPath
    in

    let goal = Proof.{ g_id = Handle.ofint root; g_pregoal = goal } in
    (goal, target, (sub, subf))

  let ipath_of_gpath (p : gpath) =
    match p with `S p -> ipath_of_path p | `P p -> p

  let of_gpath (proof : Proof.proof) (p : gpath) =
    of_ipath proof (ipath_of_gpath p)

  (* -------------------------------------------------------------------- *)
  (** Handling of polarities *)


  (** [opp p] returns the opposite polarity of [p] *)

  let opp = function
    | Pos -> Neg
    | Neg -> Pos


  (** [direct_subform_pol (p, f) i] returns the [i]th direct subformula of [f]
      together with its polarity, given that [f]'s polarity is [p] *)

  let direct_subform_pol (p, f : pol * form) (i : int) =
    match f with
    | FConn (c, fs) ->
      let subp =
        match c, i with
        | `Imp, 0 | `Not, 0 -> opp p
        | _, _ -> p
      in
      let subf =
        try List.at fs i
        with Invalid_argument _ -> raise InvalidFormPath
      in
      subp, subf
    | FBind (_, _, _, subf) ->
      p, subf
    | _ -> raise InvalidFormPath
  

  (* [subform_pol (p, f) sub] returns the subformula of [f] at path [sub] together
     with its polarity, given that [f]'s polarity is [p] *)

  let subform_pol = List.fold_left direct_subform_pol


  (* [pol_of_gpath proof p] returns the polarity of the subformula
     at path [p] in [proof] *)

  let pol_of_gpath (proof : Proof.proof) (p : gpath) : pol =
    let _, target, (sub, _) = of_gpath proof p in
    let pol, form =
      match target with
      | `H (_, { h_form = f }) -> Neg, f
      | `C f -> Pos, f
    in
    subform_pol (pol, form) sub |> fst

  (* -------------------------------------------------------------------- *)

  type asource = [
    | `Click of gpath
    | `DnD   of adnd
  ]

  and adnd = { source : gpath; destination : gpath option; }

  type osource = [
    | `Click of ipath
    | `DnD   of ipath * ipath
  ]

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


  type pnode += TLink


  let invertible (pol : pol) (f : form) : bool =
    match pol with
    (* Right invertible *)
    | Pos -> begin match f with
      | FConn (c, _) -> begin match c with
        | `Or | `Imp | `Not -> true
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


  let rec elim_units : form -> form = function

    (* Absorbing elements *)

    | FConn (`And, [_; FFalse])
    | FConn (`And, [FFalse; _])
    | FConn (`Not, [FTrue]) ->
      Form.f_false

    | FConn (`Or, [_; FTrue])
    | FConn (`Or, [FTrue; _])
    | FConn (`Imp, [_; FTrue])
    | FConn (`Imp, [FFalse; _])
    | FConn (`Not, [FFalse]) ->
      Form.f_true

    (* Neutral elements *)

    | FConn (`And, [f; FTrue])
    | FConn (`And, [FTrue; f])
    | FConn (`Or, [f; FFalse])
    | FConn (`Or, [FFalse; f])
    | FConn (`Imp, [FTrue; f]) ->
      elim_units f
    
    | FTrue | FFalse | FPred _ as f -> f
    | FConn (c, fs) as f ->
      let fs' = List.map elim_units fs in
      if fs = fs' then f else elim_units (FConn (c, fs'))

  
  (* The [close_with_unit] tactic tries to close the goal either with
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
      (fun (hd, { h_form = f }) ->
       if f = FFalse then Some (elim hd targ) else None)
    |>
    Option.default proof

  
  (** [dlink] stands for _d_eep link, and implements the deep interaction phase
      à la Chaudhuri for intuitionistic logic (propositional case for now). *)
  
  let dlink src s_src dst s_dst : tactic =
    fun (proof, g_id) ->

    let open Form in

    let rec backward : (form * int list) * (form * int list) -> form = function

      (** End rules *)

      | (h, []), (c, []) ->      
        if h = c
        
        (* lnid *)
        then f_true
        
        (* unlnp *)
        else f_imp h c

      (** Left interaction rules *)

      (* lnplc1 *)
      | (FConn (`And, [f1; f2]), 0 :: sub), (f, _ as c) ->
        backward ((f1, sub), c)

      (* lnplc2 *)
      | (FConn (`And, [f1; f2]), 1 :: sub), (f, _ as c) ->
        backward ((f2, sub), c)

      (* lnpld1 *)
      | (FConn (`Or, [f1; f2]), 0 :: sub), (f, _ as c) ->
        f_and (backward ((f1, sub), c)) (f_imp f2 f)
      
      (* lnpld2 *)
      | (FConn (`Or, [f1; f2]), 1 :: sub), (f, _ as c) ->
        f_and (f_imp f1 f) (backward ((f2, sub), c))

      (* lnpli2 *)
      | (FConn (`Imp, [f1; f2]), 1 :: sub), (f, _ as c)
        when not (invertible Pos f) ->
        f_and f1 (backward ((f2, sub), c))
        
      (** Right interaction rules *)

      (* lnprc1 *)
      | (f, _ as h), (FConn (`And, [f1; f2]), 0 :: sub)
        when not (invertible Neg f) ->
        f_and (backward (h, (f1, sub))) f2

      (* lnprc2 *)
      | (f, _ as h), (FConn (`And, [f1; f2]), 1 :: sub)
        when not (invertible Neg f) ->
        f_and f1 (backward (h, (f2, sub)))

      (* lnprd1 *)
      | (f, _ as h), (FConn (`Or, [f1; f2]), 0 :: sub) ->
        f_or (backward (h, (f1, sub))) f2

      (* lnprd2 *)
      | (f, _ as h), (FConn (`Or, [f1; f2]), 1 :: sub) ->
        f_or f1 (backward (h, (f2, sub)))

      (* lnpri1 *)
      | (f, _ as h), (FConn (`Imp, [f1; f2]), 0 :: sub) ->
        f_imp (forward (h, (f1, sub))) f2

      (* lnpri2 *)
      | (f, _ as h), (FConn (`Imp, [f1; f2]), 1 :: sub) ->
        f_imp f1 (backward (h, (f2, sub)))

      (* lnprn1 *)
      | (f, _ as h), (FConn (`Not, [f1]), 0 :: sub) ->
        f_not (forward ((h, (f1, sub))))

    and forward : (form * int list) * (form * int list) -> form = function

      (** End rules *)

      | (h, []), (h', []) ->

        (* unlnn *)
        f_and h h'

      (** Interaction rules *)

      (* lnnc1 *)
      | (f, _ as h), (FConn (`And, [f1; f2]), 0 :: sub) ->
        f_and (forward (h, (f1, sub))) f2

      (* lnnc2 *)
      | (f, _ as h), (FConn (`And, [f1; f2]), 1 :: sub) ->
        f_and f1 (forward (h, (f2, sub)))

      (* lnnd1 *)
      | (f, _ as h), (FConn (`Or, [f1; f2]), 0 :: sub) ->
        f_or (forward (h, (f1, sub))) f2

      (* lnnd2 *)
      | (f, _ as h), (FConn (`Or, [f1; f2]), 1 :: sub) ->
        f_or f1 (forward (h, (f2, sub)))

      (* lnni1 *)
      | (f, _ as h), (FConn (`Imp, [f1; f2]), 0 :: sub)
        when not (invertible Neg f) ->
        f_imp (backward (h, (f1, sub))) f2

      (* lnni2 *)
      | (f, _ as h), (FConn (`Imp, [f1; f2]), 1 :: sub)
        when not (invertible Neg f) ->
        f_imp f1 (forward (h, (f2, sub)))

      (* lnnn1 *)
      | (f, _ as h), (FConn (`Not, [f1]), 0 :: sub)
        when not (invertible Neg f) ->
        f_not (backward (h, (f1, sub)))
        
      (* lnncomm *)
      | h, h' -> forward (h', h)
    in

    let open Proof in

    let { g_pregoal = goal }, top_src, (sub_src, _) = of_ipath proof src in
    let _, top_dst, (sub_dst, _) = of_ipath proof dst in

    let subgoal = match top_src, top_dst, sub_src, sub_dst with
      | `H (_, { h_form = h }), `C c, subh, subc
      | `C c, `H (_, { h_form = h }), subc, subh ->
        [[], backward ((h, subh), (c, subc)) |> elim_units]
      
      | `H (_, { h_form = h }), `H (_, { h_form = h' }), subh, subh' ->
        [[None, [forward ((h, subh), (h', subh')) |> elim_units]], goal.g_goal]
    in

    sprogress proof g_id TLink subgoal
    |>
    fun pr -> close_with_unit (pr, List.hd (opened pr))
  

  (** [subs f] returns all the paths leading to a subformula in [f]. *)

  let subs (f : form) : (int list) list =
    let rec aux sub = function
      | FConn (_, fs) ->
        fs |> List.mapi (fun i f ->
                let sub = sub @ [i] in
                sub :: aux sub f)
           |> List.concat
      | FBind (_, _, _, f) ->
        let sub = sub @ [0] in
        sub :: aux sub f
      | _ -> [[]]
    in aux [] f


  (** [search_match env (p1, f1) (p2, f2)] returns the list of pairs of paths that lead
      to unifiable subformulas of [f1] and [f2] of opposite polarities, together with
      the associated substitutions generated by unification. *)

  let search_match env (p1, f1) (p2, f2)
    : (int list * subst * int list * subst) list =

    let module Name : Graph.Sig.COMPARABLE
      with type t = Fo.name
    = struct
      type t = Fo.name
      let equal = String.equal
      let compare = String.compare
      let hash = Hashtbl.hash
    end in
    let module Deps = struct
      include Graph.Persistent.Digraph.Concrete(Name)

      let subst : t -> subst -> t =
        (* For each item [x := e] in the substitution *)
        List.fold_left begin fun deps (x, tag) ->
          let fvs = match tag with
            | Sbound e -> Form.e_vars e
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
        end
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
      type t = Deps.t * (name * name) list * env * subst
    end in
    let module State = Monad.State(Env) in

    let rec traverse (p, f) i : (pol * form) State.t =
      let open State in
      match p, f with

      | Pos, FBind (`Forall, x, ty, f)
      | Neg, FBind (`Exist, x, ty, f) ->

        get >>= fun (deps, rnm, env, s) ->
        let y, env = Vars.bind env (x, ty) in
        let exs = List.filter_map
          (function (x, Sflex) -> Some x | _ -> None) s
        in
        let deps = List.fold_left
          (fun deps x -> Deps.add_edge deps x y)
          deps exs
        in
        let z = EVars.fresh () in
        let rnm = (z, x) :: rnm in
        let s = (z, Sbound (EVar (y, 0))) :: s in
        put (deps, rnm, env, s) >>= fun _ ->
        return (p, Form.f_subst (x, 0) (EVar (y, 0)) f)

      | Neg, FBind (`Forall, x, ty, f)
      | Pos, FBind (`Exist, x, ty, f) ->

        get >>= fun (deps, rnm, env, s) ->
        let z = EVars.fresh () in
        let rnm = (z, x) :: rnm in
        let s = (z, Sflex) :: s in
        put (deps, rnm, env, s) >>= fun _ ->
        return (p, Form.f_subst (x, 0) (EVar (z, 0)) f)

      | _ -> return (direct_subform_pol (p, f) i)
    in

    let traverse = State.fold traverse in

    let open Monad.List in

    subs f1 >>= fun sub1 ->
    subs f2 >>= fun sub2 ->

    let deps, sp1, sf1, rnm1, s1, sp2, sf2, rnm2, s2 =
      let open State in
      run begin
        traverse (p1, f1) sub1 >>= fun (sp1, sf1) ->
        get >>= fun (deps, rnm1, env, s1) ->
        put (deps, [], env, []) >>= fun _ ->

        traverse (p2, f2) sub2 >>= fun (sp2, sf2) ->
        get >>= fun (deps, rnm2, _, s2) ->

        return (deps, sp1, sf1, rnm1, s1, sp2, sf2, rnm2, s2)
      end
      (Deps.empty, [], env, [])
    in

    if sp1 <> sp2 then
      match Form.f_unify Fo.Env.empty (s1 @ s2) [sf1, sf2] with
      | Some s when acyclic (Deps.subst deps s) ->
        let s1, s2 = List.split_at (List.length s1) s in
        let rename exs = List.map (fun (x, tag) ->
          Option.default x (List.assoc_opt x exs), tag)
        in return (
          sub1, s1 |> rename rnm1 |> List.rev,
          sub2, s2 |> rename rnm2 |> List.rev)
      (* | None -> return (sub1, [], sub2, []) *)
      | None -> zero
    else zero


  let dnd_actions src dsts (proof : Proof.proof) =
    let src = ipath_of_gpath src in
    let Proof.{ g_id; g_pregoal}, _, (sub_src, f_src) = of_ipath proof src in

    let for_destination dst =
      let dst = ipath_of_gpath dst in
      let Proof.{ g_id = g_id'; _}, _, (sub_dst, f_dst) = of_ipath proof dst in
  
      if not (Handle.eq g_id g_id') then [] else
      
      let pol_src = pol_of_gpath proof (`P src) in
      let pol_dst = pol_of_gpath proof (`P dst) in

      let targets =
        search_match g_pregoal.g_env (pol_src, f_src) (pol_dst, f_dst) |>
        List.map (fun (sub1, s1, sub2, s2) ->
          mk_ipath ~ctxt:src.ctxt ~sub:(sub_src @ sub1) src.root, s1,
          mk_ipath ~ctxt:dst.ctxt ~sub:(sub_dst @ sub2) dst.root, s2)
      in

      List.map (fun (src, s_src, tgt, s_tgt) ->
        "Link", [src; tgt], `DnD (src, tgt), (g_id, `Link (src, s_src, tgt, s_tgt)))
        targets
    in
    match dsts with
    | None ->
      (* Get the list of hypotheses handles *)
      let dsts = Proof.Hyps.ids g_pregoal.Proof.g_hyps in
      (* Create a list of paths to each hypothesis *)
      let dsts =
        List.map
          (fun id -> mk_ipath (Handle.toint g_id) ~ctxt:(Handle.toint id))
          dsts
      in
      (* Add a path to the conclusion *)
      let dsts = mk_ipath (Handle.toint g_id) :: dsts in
      let dsts = List.map (fun p -> `P p) dsts in
      (* Remove [src] from the list of paths *)
      let dsts = List.remove dsts (`P src) in
      (* Get the possible actions for each formula in the goal,
         that is the hypotheses and the conclusion *)
      List.flatten (List.map for_destination dsts)

    | Some dst ->
      for_destination dst


  let dnD_actions src dsts (proof : Proof.proof) =
    begin
      let module E = struct exception Nothing end in

      let Proof.{ g_id = hd1; g_pregoal = pr}, tg1, _ = of_gpath proof src in

      let for_destination (dst : gpath) =
        try
          let Proof.{ g_id = hd2; _}, tg2, _ = of_gpath proof dst in
  
          if not (Handle.eq hd1 hd2) then
            raise E.Nothing;
  
          match tg1, tg2 with
          | `H (tg1, { h_form = f1; _ }),
            `H (tg2, { h_form = ((FConn (`Imp, [_; _])) | (FBind (`Forall, _, _, _))) as f; _})
              when not (Handle.eq tg1 tg2) 
            -> 
            begin
              let (hl, fc, s) = prune_premisses_fad f in
              let rec f_aux i = function
                | [] -> []
                | (s, g)::l -> match Form.search_match_p s g f1 with
                | Some (s, pt) ->
                  let aux_c = f_aux (i+1) l in
                  (i, s, pt)::aux_c (* we look for other matches here *)
                | None -> f_aux (i+1) l 
              in 
              let build_action (i, sr, pt) =
                let path = ref [] in
                let rec rebuild_path j p = function
                  | FBind (`Forall, _, _, f) -> rebuild_path j (0::p) f
                  | FConn (`Imp, [_ ; f2] ) ->
                    if j = 0 
                    then p
                   else rebuild_path (j-1) (1::p) f2
                in 
                let p = (List.rev (rebuild_path i [] f)@[0]@pt) in
                let src = mk_ipath (Handle.toint hd1) ~ctxt:(Handle.toint tg1) in
                let dst = mk_ipath (Handle.toint hd1) ~ctxt:(Handle.toint tg2)  ~sub:(p)  in
                let dst' = match dsts with
                  | None -> ipath_strip dst
                  | _ -> dst
                in
                let aui = `DnD (src, dst) in  (* C'est ici que ça se passe *)
                ("Forward", [dst'], aui, (hd1, `Forward (tg1, tg2, p, sr)))
              in
              List.map build_action (f_aux 0 hl)
            end 
 
          | `H (tg1, { h_form = f1; _ }), `C f2 ->
            let (hl, subf1, s) = prune_premisses_fa f1 in
            begin
              match Form.search_match_f s subf1 f2 with
              | Some (sr, pt) when Form.s_complete sr ->
                let pres = List.map (Form.iter_subst sr) hl in
                let src = mk_ipath (Handle.toint hd1) ~ctxt:(Handle.toint tg1) in
                let dst = mk_ipath (Handle.toint hd2) ~sub:(pt) in
                let aui = `DnD (ipath_strip src, ipath_strip dst) in

                ["Elim", [dst], aui, (hd1, `Elim tg1)]

              | None ->
                let (hl, goal, s) = prune_premisses_ex f2 in
                let pre, hy = prune_premisses f1 in
                match Form.search_match_p s goal hy with
                | Some (sr, pt) when Form.s_complete sr ->
                  let pt = (rebuild_path (List.length sr - 1))@pt in 
                  let src = mk_ipath (Handle.toint hd1) ~ctxt:(Handle.toint tg1) in
                  let dst = mk_ipath (Handle.toint hd1) ~sub:(pt) in
                  let aui = `DnD (src, dst) in

                  ["DisjDrop",  [dst], aui, (hd1, `DisjDrop (tg1,pre) )]

              | _ -> raise E.Nothing
            end
            (*
              if Form.f_equal subf1 f2 then
                let src = mk_ipath (Handle.toint hd1) ~ctxt:(Handle.toint tg1) in
                let dst = mk_ipath (Handle.toint hd1) in
                let aui = `DnD (ipath_strip src, ipath_strip dst) in

                ["Elim", [dst], aui, (hd1, `Elim tg1)]
              else 
                let dld = Form.flatten_disjunctions f2 in
                let dlc = Form.flatten_conjunctions f2 in

                begin match List.findex (Form.f_equal f1) dld,
                            List.findex (Form.f_equal f1) dlc  with
                | Some i, _  ->
                    let path = rebuild_pathd (List.length dld) i in
                    let src = mk_ipath (Handle.toint hd1) ~ctxt:(Handle.toint tg1) in
                    let dst = mk_ipath (Handle.toint hd1) ~sub:(path) in
                    let aui = `DnD (ipath_strip src, ipath_strip dst) in

                    ["DisjDrop",  [dst], aui, (hd1, `DisjDrop tg1 )]

                | _, Some i ->
                    let path = rebuild_pathd (List.length dlc) i in
                    let src = mk_ipath (Handle.toint hd1) ~ctxt:(Handle.toint tg1) in
                    let dst = mk_ipath (Handle.toint hd1) ~sub:(path) in
                    let aui = `DnD (ipath_strip src, ipath_strip dst) in

                    ["ConjDrop",  [dst], aui, (hd1, `ConjDrop tg1 )]

                | None, None -> raise E.Nothing end
            *)
          | _ -> raise E.Nothing
  
        with E.Nothing -> []
      in
      match dsts with
      | None ->
        (* Get the list of hypotheses handles *)
        let dsts = Proof.Hyps.ids pr.Proof.g_hyps in
        (* Create a list of paths to each hypothesis *)
        let dsts =
          List.map
            (fun id -> mk_ipath (Handle.toint hd1) ~ctxt:(Handle.toint id))
            dsts
        in
        (* Add a path to the conclusion *)
        let dsts = mk_ipath (Handle.toint hd1) :: dsts in
        let dsts = List.map (fun p -> `P p) dsts in
        (* Get the possible actions for each formula in the goal,
           that is the hypotheses and the conclusion *)
        List.flatten (List.map for_destination dsts)

      | Some dst ->
        for_destination dst
    end
      
  let actions (proof : Proof.proof) (p : asource)
      : (string * ipath list * osource * action) list
  =
    match p with
      | `Click p -> begin
          let Proof.{ g_id = hd; g_pregoal = _goal}, target, (_fs, _subf) =
            of_gpath proof p
          in
          match target with
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

      | `DnD { source = src; destination = dsts; } ->
        dnd_actions src dsts proof 

  
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
    | `Link (src, s, dst, s') ->
        dlink src s dst s' (proof, hd)
end
