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

  type hyp = {
    h_src  : Handle.t option;
    h_gen  : int;
    h_form : form;
  }

  type hyps = (Handle.t, hyp) Map.t

  module Hyps : sig
    val byid : hyps -> Handle.t -> hyp
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

  type hyp = {
    h_src  : Handle.t option;
    h_gen  : int;
    h_form : form;
  }

  type hyps = (Handle.t, hyp) Map.t

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

  module Hyps = struct
    let byid (hyps : hyps) (id : Handle.t) =
      Option.get_exn
        (Map.Exceptionless.find id hyps)
        (InvalidHyphId id)
  end

  let mk_hyp ?(src : Handle.t option) ?(gen : int = 0) form =
    { h_src = src; h_gen = gen; h_form = form; }

  let init (env : env) (goal : form) =
    Form.recheck env goal;

    let uid  = Handle.fresh () in
    let root = { g_id = uid; g_pregoal = {
        g_env  = env;
        g_hyps = Map.empty;
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
        let hyps = Map.map (fun h -> { h with h_gen = h.h_gen + 1 }) sub.g_hyps in
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

  let sprogress (pr : proof) ?(clear = false) (id : Handle.t) (pn : pnode) sub =
    let goal = byid pr id in

    let for1 (newlc, concl) =
      let subfor1 hyps (hid, newlc) =
        let hyps =
          Option.fold (fun hyps hid ->
            let _h = (Hyps.byid hyps hid).h_form in
            if clear then Map.remove hid hyps else hyps)
          hyps hid in
        let hsrc = if clear then None else hid in

        let hyps = List.fold_left (fun hyps newh ->
            Map.add (Handle.fresh ()) (mk_hyp ?src:hsrc newh) hyps)
          hyps newlc
        in hyps in

      let hyps = List.fold_left subfor1 goal.g_hyps newlc in
      { g_env = goal.g_env; g_hyps = hyps; g_goal = concl; }

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
  type ipath  = { root : int; ctxt : int; sub : int list; }
  type gpath  = [`S of path | `P of ipath]

  val cut       : Fo.form -> tactic
  val intro     : ?variant:int -> tactic
  val elim      : ?clear:bool -> Handle.t -> tactic
  val ivariants : targ -> string list
  val forward   : (Handle.t * Handle.t) -> tactic

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
    | `Forward of Handle.t * Handle.t
    | `DisjDrop of Handle.t
    | `ConjDrop of Handle.t
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

  type pnode += TIntro

  let prune_premisses =
    let rec doit acc = function
      | FConn (`Imp, [f1; f2]) -> doit (f1 :: acc) f2
      | f -> (List.rev acc, f)
    in fun f -> doit [] f

  let rec remove_form f = function
      | [] -> raise TacticNotApplicable
      | g::l when Form.equal g f -> l
      | g::l -> g::(remove_form f l)

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

  type pnode += OrDrop of Handle.t

  let or_drop (h : Handle.t) ((pr, id) : targ) =
    let gl   = Proof.byid pr id in
    let _hy  = (Proof.Hyps.byid gl.g_hyps h).h_form in
    let _gll = Form.flatten_disjunctions gl.g_goal in
    Proof.sprogress pr id (OrDrop id) []

  type pnode += AndDrop of Handle.t

  let and_drop (h : Handle.t) ((pr, id) : targ) =
    let gl  = Proof.byid pr id in
    let hy  = (Proof.Hyps.byid gl.g_hyps h).h_form in
    let gll = Form.flatten_disjunctions gl.g_goal in
    let ng  = Form.f_ands (remove_form hy gll) in

    Proof.sprogress pr id (AndDrop id) [[None, []], ng]

  type pnode += TElim of Handle.t

  let elim ?clear (h : Handle.t) ((pr, id) : targ) =
    let gl = Proof.byid pr id in
    let hy = (Proof.Hyps.byid gl.g_hyps h).h_form in

    let pre, hy = prune_premisses hy in
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
    let src = (Proof.Hyps.byid gl.g_hyps hsrc).h_form in
    let dst = (Proof.Hyps.byid gl.g_hyps hdst).h_form in

    match dst with
      | FConn (`Imp, [_; _]) as f0 ->
          let (hf, cf) = prune_premisses f0 in
          let nhf = remove_form src hf in
          let nf = Form.f_imps nhf cf in
            Proof.sprogress pr ~clear:true id (TForward (hsrc, hdst))
              ([[Some hdst, [nf]], gl.g_goal])

    | _ -> raise TacticNotApplicable

  type pnode += TCut of Fo.form * Handle.t

  let cut (form : form) ((proof, hd) : targ) =
    let goal = Proof.byid proof hd in

    Fo.Form.recheck goal.g_env form;

    let subs = [[], form] in
    
    Proof.sprogress proof hd (TCut (form, hd))
      (subs @ [[None, [form]], goal.g_goal])

  type action = Handle.t * [
    | `Elim    of Handle.t
    | `Intro   of int
    | `Forward of Handle.t * Handle.t
    | `DisjDrop of Handle.t
    | `ConjDrop of Handle.t
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

    | _ ->
        raise InvalidFormPath

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

  let of_ipath (proof : Proof.proof) (p : ipath) =
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

    in (goal, Handle.ofint root, target, (sub, subf))

  let ipath_of_gpath (p : gpath) =
    match p with `S p -> ipath_of_path p | `P p -> p

  let of_gpath (proof : Proof.proof) (p : gpath) =
    of_ipath proof (ipath_of_gpath p)

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

  let actions (proof : Proof.proof) (p : asource)
      : (string * ipath list * osource * action) list
  =
    match p with
    | `Click p -> begin
      let _goal, hd, target, (_fs, _subf) = of_gpath proof p in
  
      match target with
      | `C _ -> begin
          let iv = ivariants (proof, hd) in
          let bv = List.length iv <= 1 in
  
          List.mapi
            (fun i x ->
              let sub = if bv then None else Some i in
              let sub = List.of_option sub in
              let hg  = mk_ipath (Handle.toint hd) ~sub:sub in
              (x, [hg], `Click hg, (hd, `Intro i)))
            iv
        end
  
      | `H (rp, _) ->
          let hg = mk_ipath (Handle.toint hd) ~ctxt:(Handle.toint rp) in
          ["Elim", [hg], `Click hg, (hd, `Elim rp)]
      end

    | `DnD { source = src; destination = dsts; } -> begin
      let module E = struct exception Nothing end in

      let pr, hd1, tg1, _ = of_gpath proof src in

      let for_destination (dst : gpath) =
        try
          let _, hd2, tg2, _ = of_gpath proof dst in
  
          if not (Handle.eq hd1 hd2) then
            raise E.Nothing;
  
          match tg1, tg2 with
          | `H (tg1, { h_form = f1; _ }),
            `H (tg2, { h_form = (FConn (`Imp, [_; _])) as f; _})
              when not (Handle.eq tg1 tg2) 
            ->
      
              let (hl, _) = prune_premisses f in

              begin match List.findex (Form.equal f1) hl with
              | None -> raise E.Nothing
              | Some i ->
                  let path = rebuild_path i in
                  let src = mk_ipath (Handle.toint hd1) ~ctxt:(Handle.toint tg1) in
                  let dst = mk_ipath (Handle.toint hd1) ~ctxt:(Handle.toint tg2)  ~sub:(path)  in
                  let aui = `DnD (ipath_strip src, ipath_strip dst) in
                  ["Forward", [dst], aui, (hd1, `Forward (tg1, tg2))] end

         | `H (tg1, { h_form = f1; _ }), `C f2 ->
              let _, subf1 = prune_premisses f1 in

              if Form.equal subf1 f2 then
                let src = mk_ipath (Handle.toint hd1) ~ctxt:(Handle.toint tg1) in
                let dst = mk_ipath (Handle.toint hd1) in
                let aui = `DnD (ipath_strip src, ipath_strip dst) in

                ["Elim", [dst], aui, (hd1, `Elim tg1)]
              else 
                let dld = Form.flatten_disjunctions f2 in
                let dlc = Form.flatten_conjunctions f2 in

                begin match List.findex (Form.equal f1) dld, List.findex (Form.equal f1) dlc  with
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

         | _ -> raise E.Nothing
  
        with E.Nothing -> [] in

      match dsts with
      | None ->
          let dsts = List.of_enum (Map.keys pr.Proof.g_hyps) in
          let dsts =
            List.map
              (fun id -> mk_ipath (Handle.toint hd1) ~ctxt:(Handle.toint id))
              dsts in
          let dsts = mk_ipath (Handle.toint hd1) :: dsts in
          let dsts = List.map (fun p -> `P p) dsts in
          List.flatten (List.map for_destination dsts)

      | Some dst ->
          for_destination dst
    end

  let apply (proof : Proof.proof) ((hd, a) : action) =
    match a with
    | `Intro variant ->
        intro ~variant (proof, hd)
    | `Elim subhd ->
        elim subhd (proof, hd)
    | `DisjDrop subhd ->
        or_drop subhd (proof, hd)
    | `ConjDrop subhd ->
        and_drop subhd (proof, hd)    
    | `Forward (src, dst) ->
        forward (src, dst) (proof, hd)
end
