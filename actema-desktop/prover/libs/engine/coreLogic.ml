open Fo
open Utils

exception TacticNotApplicable

type targ = Proof.proof * Handle.t
type tactic = targ -> Proof.proof

let add_local ((name, ty, body) : string * Fo.type_ * Fo.expr option) (goal : Proof.pregoal) :
    Proof.pregoal =
  Option.map_default (Fo.Form.erecheck goal.g_env ty) () body;

  let g_env = Fo.Vars.push goal.g_env (name, (ty, body)) in
  let g_env = Fo.Vars.map g_env (Option.map (Fo.Form.e_shift (name, 0))) in

  let g_hyps =
    Proof.Hyps.(map (fun h -> { h with h_form = Form.f_shift (name, 0) h.h_form }) goal.g_hyps)
  in

  let g_goal = Form.f_shift (name, 0) goal.g_goal in

  { g_env; g_hyps; g_goal }

let add_local_def ((name, ty, body) : string * Fo.type_ * Fo.expr) ((proof, hd) : targ) =
  let new_goal = add_local (name, ty, Some body) (Proof.byid proof hd) in
  snd @@ Proof.xprogress proof hd [ new_goal ]

let ivariants ((pr, id) : targ) =
  match (Proof.byid pr id).g_goal with
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

let evariants ((pr, id) : targ) hd =
  match (Proof.Hyps.byid (Proof.byid pr id).g_hyps hd).h_form with
  | FPred ("_EQ", _) -> [ "rewrite->"; "rewrite<-" ]
  | FTrue -> [ "destruct" ]
  | FFalse -> [ "destruct" ]
  | FConn (`And, _) -> [ "destruct" ]
  | FConn (`Or, _) -> [ "destruct" ]
  | FConn (`Imp, _) -> [ "apply" ]
  | FConn (`Not, _) -> [ "destruct" ]
  | FBind (`Exist, _, _, _) -> [ "destruct" ]
  | _ -> []

let generalize (hid : Handle.t) ((proof, id) : targ) =
  let goal = Proof.byid proof id in
  let hyp = (Proof.Hyps.byid goal.g_hyps hid).h_form in

  snd
  @@ Proof.xprogress proof id
       [ { g_env = goal.g_env
         ; g_hyps = Proof.Hyps.remove goal.g_hyps hid
         ; g_goal = FConn (`Imp, [ hyp; goal.g_goal ])
         }
       ]

let move (from : Handle.t) (before : Handle.t option) ((proof, id) : targ) =
  let goal = Proof.byid proof id in
  let _from = Proof.Hyps.byid goal.g_hyps in
  (* KEEP *)
  let _before = Option.map (Proof.Hyps.byid goal.g_hyps) before in
  (* KEEP *)
  let hyps = Proof.Hyps.move goal.g_hyps from before in

  snd @@ Proof.xprogress proof id [ { goal with g_hyps = hyps } ]

(* -------------------------------------------------------------------- *)
(** Items *)

type item = [ `C of form | `H of Handle.t * Proof.hyp | `V of vname * bvar ]

let form_of_item : item -> form = function
  | `C f | `H (_, Proof.{ h_form = f; _ }) -> f
  | _ -> raise (Invalid_argument "Expected a formula item")

let expr_of_item ?(where = `Body) : item -> expr = function
  | `V (x, (_, b)) -> begin
      match where with
      | `Head -> EVar x
      | `Body -> Option.get_exn b (Invalid_argument "Expected a local variable with a body")
    end
  | _ -> raise (Invalid_argument "Expected an expression item")

let term_of_item ?where it =
  try `F (form_of_item it)
  with Invalid_argument _ -> (
    try `E (expr_of_item ?where it)
    with Invalid_argument _ -> raise (Invalid_argument "Expected an expression or formula item"))

(* -------------------------------------------------------------------- *)
(** Paths *)

type path = string
type pkind = [ `Hyp | `Concl | `Var of [ `Head | `Body ] ]
type ctxt = { kind : pkind; handle : int }
type ipath = { root : int; ctxt : ctxt; sub : int list }

exception InvalidPath of path
exception InvalidSubFormPath of int list
exception InvalidSubExprPath of int list

let direct_subterm (t : term) (i : int) : term =
  let open Form in
  try List.at (direct_subterms t) i
  with Invalid_argument _ -> (
    match t with
    | `F (FPred _) | `E _ -> raise (InvalidSubExprPath [ i ])
    | `F _ -> raise (InvalidSubFormPath [ i ]))

let subterm (t : term) (p : int list) =
  try List.fold_left direct_subterm t p with
  | InvalidSubFormPath _ -> raise (InvalidSubFormPath p)
  | InvalidSubExprPath _ -> raise (InvalidSubExprPath p)

let modify_direct_subterm (f : term -> term) (t : term) (i : int) : term =
  let open Form in
  try List.modify_at i f (direct_subterms t) |> modify_direct_subterms t
  with Invalid_argument _ -> (
    match t with
    | `F (FPred _) | `E _ -> raise (InvalidSubExprPath [ i ])
    | `F _ -> raise (InvalidSubFormPath [ i ]))

let modify_subterm (f : 'a -> term -> term) (acc : int -> term -> 'a -> 'a) (a : 'a) (t : term)
    (p : int list) : term =
  let rec aux a t = function
    | [] -> f a t
    | i :: p ->
        let subt = aux (acc i t a) (direct_subterm t i) p in
        modify_direct_subterm (fun _ -> subt) t i
  in
  aux a t p

(** [rewrite_subterm_all env red res t sub] rewrites all occurrences of [red]
      in the subterm of [t] at subpath [sub] into [res], shifting variables in
      [red] and [res] whenever a binder is encountered along the path. *)
let rewrite_subterm_all env red res =
  modify_subterm
    (fun (red, res) -> Form.rewrite env red res)
    (fun _ t (red, res) -> Form.(shift_under t red, shift_under t res))
    (red, res)

(** [rewrite_subterm res t sub] rewrites the subterm of [t] at subpath
      [sub] into [res], shifting variables in [res] whenever a binder is
      encountered along the path. *)
let rewrite_subterm res =
  modify_subterm (fun res _ -> res) (fun _ t res -> Form.shift_under t res) res

let subform (f : form) (p : int list) =
  match subterm (`F f) p with `F f -> f | _ -> raise (InvalidSubFormPath p)

let subexpr (t : term) (p : int list) =
  match subterm t p with `E e -> e | _ -> raise (InvalidSubExprPath p)

let rebuild_path i =
  let rec aux l = function 0 -> 0 :: l | i -> aux (1 :: l) (i - 1) in
  List.rev (aux [] i)

let rebuild_pathd l i =
  if i + 1 = l
  then [ 1 ]
  else
    let rec aux = function 0 -> [] | i -> 0 :: aux (i - 1) in
    if i = 0 then aux (l - 1) else aux (l - i - 1) @ [ 1 ]

let mk_ipath ?(ctxt : ctxt = { kind = `Concl; handle = 0 }) ?(sub : int list = []) (root : int) =
  { root; ctxt; sub }

let item_ipath { root; ctxt; _ } = { root; ctxt; sub = [] }
let concl_ipath Proof.{ g_id; _ } = mk_ipath (Handle.toint g_id)

let all_hyps_ipaths Proof.{ g_id; g_pregoal } =
  (* Get the list of hypotheses handles *)
  Proof.Hyps.ids g_pregoal.Proof.g_hyps
  |> (* Create a list of paths to each hypothesis *)
  List.map
    begin
      fun hd -> mk_ipath (Handle.toint g_id) ~ctxt:{ kind = `Hyp; handle = Handle.toint hd }
    end

let all_vars_ipaths ?(heads = true) Proof.{ g_id; g_pregoal } =
  let env = g_pregoal.Proof.g_env in
  (* Get the list of variable handles *)
  env.env_handles |> BiMap.codomain
  |> (* Create a list of paths to each variable's head and body *)
  List.concat_map
    begin
      fun hd ->
        (if heads
         then [ mk_ipath (Handle.toint g_id) ~ctxt:{ kind = `Var `Head; handle = Handle.toint hd } ]
         else [])
        @
        match Vars.byid env hd with
        | Some (_, (_, Some _)) ->
            [ mk_ipath (Handle.toint g_id) ~ctxt:{ kind = `Var `Body; handle = Handle.toint hd } ]
        | _ -> []
    end

let all_items_ipaths ?heads goal =
  (concl_ipath goal :: all_hyps_ipaths goal) @ all_vars_ipaths ?heads goal

let pkind_codes : (pkind, string) BiMap.t =
  List.fold_left
    (fun m (a, b) -> BiMap.add a b m)
    BiMap.empty
    [ (`Hyp, "H"); (`Concl, "C"); (`Var `Head, "Vh"); (`Var `Body, "Vb") ]

let string_of_pkind : pkind -> string = BiMap.find ^~ pkind_codes
let pkind_of_string : string -> pkind = BiMap.find ^~ BiMap.inverse pkind_codes

let path_of_ipath (p : ipath) =
  let pp_sub =
    Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "/") Format.pp_print_int
  in
  Format.asprintf "%d/%s#%d:%a" p.root (string_of_pkind p.ctxt.kind) p.ctxt.handle pp_sub p.sub

let ipath_of_path (p : path) =
  let root, ({ handle; _ } as ctxt), sub =
    try
      Scanf.sscanf p "%d/%s@#%d:%s" (fun x1 x2 x3 x4 ->
          (x1, { kind = pkind_of_string x2; handle = x3 }, x4))
    with Scanf.Scan_failure _ | Not_found | End_of_file -> raise (Invalid_argument p)
  in

  if root < 0 || handle < 0 then raise (InvalidPath p);

  let sub =
    let sub = if sub = "" then [] else String.split_on_char '/' sub in

    try List.map int_of_string sub with Failure _ -> raise (InvalidPath p)
  in

  if List.exists (fun x -> x < 0) sub then raise (InvalidPath p);

  { root; ctxt; sub }

let of_ipath (proof : Proof.proof) (p : ipath) : Proof.goal * item * (uid list * term) =
  let exn = InvalidPath (path_of_ipath p) in

  let { root; ctxt; sub } = p in

  let goal = try Proof.byid proof (Handle.ofint root) with Proof.InvalidGoalId _ -> raise exn in

  let item, t_item =
    match (ctxt.kind, ctxt.handle) with
    | `Concl, 0 ->
        let f = goal.Proof.g_goal in
        (`C f, `F f)
    | `Hyp, hd -> begin
        try
          let rp = Handle.ofint hd in
          let ({ Proof.h_form = hf; _ } as hyd) = Proof.Hyps.byid goal.Proof.g_hyps rp in
          (`H (rp, hyd), `F hf)
        with Proof.InvalidHyphId _ -> raise exn
      end
    | `Var part, hd ->
        let ((x, (_, body)) as def) = Option.get_exn (Vars.byid goal.g_env (Handle.ofint hd)) exn in
        let expr = match part with `Head -> EVar x | `Body -> Option.get_exn body exn in
        (`V def, `E expr)
    | _ -> raise exn
  in
  let target = subterm t_item sub in

  let goal = Proof.{ g_id = Handle.ofint root; g_pregoal = goal } in
  (goal, item, (sub, target))

let goal_of_ipath (proof : Proof.proof) (p : ipath) : Proof.goal =
  let g, _, _ = of_ipath proof p in
  g

let gid_of_ipath (proof : Proof.proof) (p : ipath) : Handle.t = (goal_of_ipath proof p).g_id

let term_of_ipath (proof : Proof.proof) (p : ipath) : term =
  let _, _, (_, t) = of_ipath proof p in
  t

let env_of_ipath (proof : Proof.proof) (p : ipath) : env =
  let goal, item, (sub, _) = of_ipath proof p in
  let env = goal.g_pregoal.g_env in
  match item with
  | `V _ -> env
  | `H (_, Proof.{ h_form = f; _ }) | `C f ->
      let rec aux env t sub =
        match sub with
        | [] -> env
        | i :: sub -> (
            match (t, i) with
            | `E _, _ -> env
            | `F (FBind (_, x, ty, f)), 0 -> aux (Vars.push env (x, (ty, None))) (`F f) sub
            | `F _, _ -> aux env (direct_subterm t i) sub)
      in
      aux env (`F f) sub

let is_sub_path (p : ipath) (sp : ipath) =
  p.root = sp.root && p.ctxt.handle = sp.ctxt.handle
  && (p.ctxt.kind = sp.ctxt.kind || (p.ctxt.kind = `Var `Head && sp.ctxt.kind = `Var `Body))
  && List.is_prefix sp.sub p.sub

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
let opp = function Pos -> Neg | Neg -> Pos | Sup -> Sup

(** [direct_subform_pol (p, f) i] returns the [i]th direct subformula of [f]
      together with its polarity, given that [f]'s polarity is [p] *)
let direct_subform_pol ((p, f) : pol * form) (i : int) =
  match f with
  | FConn (c, fs) ->
      let subp = match (c, i) with `Imp, 0 | `Not, 0 -> opp p | `Equiv, _ -> Sup | _, _ -> p in
      let subf = try List.at fs i with Invalid_argument _ -> raise (InvalidSubFormPath [ i ]) in
      (subp, subf)
  | FBind (_, _, _, subf) -> (p, subf)
  | _ -> raise (InvalidSubFormPath [ i ])

let direct_subterm_pol ((p, t) : pol * term) (i : int) =
  match (t, direct_subterm t i) with
  | `F f, `F _ ->
      let p, f = direct_subform_pol (p, f) i in
      (p, `F f)
  | _, t -> (p, t)

(** [subform_pol (p, f) sub] returns the subformula of [f] at path [sub] together
      with its polarity, given that [f]'s polarity is [p] *)
let subform_pol (p, f) sub =
  try List.fold_left direct_subform_pol (p, f) sub
  with InvalidSubFormPath _ -> raise (InvalidSubFormPath sub)

(** [neg_count f sub] counts the number of negations in [f] along path [sub] *)
let neg_count (f : form) (sub : int list) : int =
  let rec aux (n, f) = function
    | [] -> n
    | i :: sub -> begin
        match f with
        | FConn (c, fs) ->
            let n = match (c, i) with `Imp, 0 | `Not, 0 -> n + 1 | _ -> n in
            let subf =
              try List.at fs i with Invalid_argument _ -> raise (InvalidSubFormPath sub)
            in
            aux (n, subf) sub
        | FBind (_, _, _, subf) -> aux (n, subf) sub
        | _ -> n
      end
  in
  aux (0, f) sub

(** [pol_of_item it] returns the polarity of the item [it] *)
let pol_of_item = function `H _ -> Neg | `C _ -> Pos | `V _ -> Neg

(** [pol_of_ipath proof p] returns the polarity of the subformula
      at path [p] in [proof] *)
let pol_of_ipath (proof : Proof.proof) (p : ipath) : pol =
  let _, item, (sub, _) = of_ipath proof p in
  let pol, form =
    match item with
    | `H (_, { h_form = f; _ }) -> (Neg, f)
    | `C f -> (Pos, f)
    | `V _ -> raise (InvalidSubFormPath sub)
  in
  subform_pol (pol, form) sub |> fst

(* -------------------------------------------------------------------- *)
(** Linking *)

type link = ipath * ipath
type hyperlink = ipath list * ipath list

let hyperlink_of_link : link -> hyperlink = fun (src, dst) -> ([ src ], [ dst ])

type choice = int * (LEnv.lenv * LEnv.lenv * expr) option
type itrace = choice list

let print_choice env ((side, witness) : choice) : string =
  let side = if side = 0 then "←" else "→" in
  let witness =
    witness
    |> Option.map_default
         (fun (le1, le2, e) ->
           let print (x, ty) = Printf.sprintf "%s : %s" x (Notation.t_tostring env ty) in
           let le1 = List.to_string print (LEnv.bindings le1) in
           let le2 = List.to_string print (LEnv.bindings le2) in
           let e = Fo.Notation.e_tostring env e in
           Printf.sprintf "%s%s{%s}" le1 le2 e)
         ""
  in
  Printf.sprintf "%s%s" side witness

let print_itrace env : itrace -> string =
  Utils.List.to_string (print_choice env) ~left:"" ~right:"" ~sep:" "

(** [link] is the equivalent of Proof by Pointing's [finger_tac], but using
      the interaction rules specific to subformula linking. *)
let link ((src, dst) : link) ((s_src, s_dst) : Form.Subst.subst * Form.Subst.subst) : tactic =
 fun (proof, hd) ->
  assert (src.ctxt <> dst.ctxt);

  let s_src = Form.Subst.aslist s_src in
  let s_dst = Form.Subst.aslist s_dst in

  let goal = Proof.byid proof hd in
  let _, item_src, (sub_src, _) = of_ipath proof src in
  let _, item_dst, (sub_dst, _) = of_ipath proof dst in

  let rec pbp (goal, ogoals) (tgt : item) sub s tgt' sub' s' =
    let gen_subgoals target sub_goal sub_ogoals =
      let ogoals = Proof.sgprogress goal sub_ogoals in
      let goal =
        let goal = List.hd (Proof.sgprogress goal [ sub_goal ]) in
        match target with
        | `H (uid, hyp) -> { goal with g_hyps = Proof.Hyps.add goal.g_hyps uid hyp }
        | _ -> goal
      in
      (goal, ogoals)
    in

    let invertible (pol : pol) (f : form) : bool =
      match pol with
      (* Right invertible *)
      | Pos -> begin
          match f with
          | FConn (c, _) -> begin match c with `And | `Imp | `Not -> true | _ -> false end
          | FBind (`Forall, _, _, _) -> true
          | _ -> false
        end
      (* Left invertible *)
      | Neg -> begin
          match f with
          | FConn (c, _) -> begin match c with `And | `Or -> true | _ -> false end
          | FBind _ -> true
          | _ -> false
        end
      | Sup -> assert false
    in

    let right_inv_rules f i sub s tgt' sub' s' =
      let tgt, (goal, new_ogoals), s =
        begin
          match (f, i + 1) with
          (* And *)
          | FConn (`And, [ f1; f2 ]), 1 ->
              let tgt = `C f1 in
              let subgoals = gen_subgoals tgt ([], f1) [ ([], f2) ] in
              (tgt, subgoals, s)
          | FConn (`And, [ f1; f2 ]), 2 ->
              let tgt = `C f2 in
              let subgoals = gen_subgoals tgt ([], f2) [ ([], f1) ] in
              (tgt, subgoals, s)
          (* Imp *)
          | FConn (`Imp, [ f1; f2 ]), 1 ->
              let tgt = `H (Handle.fresh (), Proof.mk_hyp f1) in
              let subgoals = gen_subgoals tgt ([], f2) [] in
              (tgt, subgoals, s)
          | FConn (`Imp, [ f1; f2 ]), 2 ->
              let tgt = `C f2 in
              let subgoals = gen_subgoals tgt ([ (None, [ f1 ]) ], f2) [] in
              (tgt, subgoals, s)
          (* Not *)
          | FConn (`Not, [ f1 ]), 1 ->
              let tgt = `H (Handle.fresh (), Proof.mk_hyp f1) in
              let subgoals = gen_subgoals tgt ([], Form.f_false) [] in
              (tgt, subgoals, s)
          (* Forall *)
          | FBind (`Forall, x, ty, f), 1 -> begin
              match List.pop_assoc x s with
              | s, Sbound (EVar (z, _)) ->
                  let f = Form.Subst.f_apply1 (x, 0) (EVar (z, 0)) f in
                  let tgt = `C f in
                  let goal, ogoals = gen_subgoals tgt ([], f) [] in
                  let goal = { goal with g_env = Vars.push goal.g_env (z, (ty, None)) } in
                  (tgt, (goal, ogoals), s)
              | _ -> raise TacticNotApplicable
            end
          | _ -> raise TacticNotApplicable
        end
      in
      pbp (goal, ogoals @ new_ogoals) tgt sub s tgt' sub' s'
    in

    let left_inv_rules f src i sub s tgt' sub' s' =
      let tgt, (goal, new_ogoals), s =
        begin
          match (f, i + 1) with
          (* And *)
          | FConn (`And, [ f1; f2 ]), 1 ->
              let tgt = `H (Handle.fresh (), Proof.mk_hyp f1 ~src) in
              let subgoals = gen_subgoals tgt ([ (Some src, [ f2 ]) ], goal.g_goal) [] in
              (tgt, subgoals, s)
          | FConn (`And, [ f1; f2 ]), 2 ->
              let tgt = `H (Handle.fresh (), Proof.mk_hyp f2 ~src) in
              let subgoals = gen_subgoals tgt ([ (Some src, [ f1 ]) ], goal.g_goal) [] in
              (tgt, subgoals, s)
          (* Or *)
          | FConn (`Or, [ f1; f2 ]), 1 ->
              let tgt = `H (Handle.fresh (), Proof.mk_hyp f1 ~src) in
              let subgoals =
                gen_subgoals tgt ([], goal.g_goal) [ ([ (Some src, [ f2 ]) ], goal.g_goal) ]
              in
              (tgt, subgoals, s)
          | FConn (`Or, [ f1; f2 ]), 2 ->
              let tgt = `H (Handle.fresh (), Proof.mk_hyp f2 ~src) in
              let subgoals =
                gen_subgoals tgt ([], goal.g_goal) [ ([ (Some src, [ f1 ]) ], goal.g_goal) ]
              in
              (tgt, subgoals, s)
          (* Forall *)
          | FBind (`Forall, x, _, f), 1 ->
              let s, item = List.pop_assoc x s in
              let tgt, subgoals =
                match item with
                | Sbound t ->
                    let f = Form.Subst.f_apply1 (x, 0) t f in
                    let tgt = `H (Handle.fresh (), Proof.mk_hyp f ~src) in
                    (tgt, gen_subgoals tgt ([], goal.g_goal) [])
                | Sflex -> failwith "cannot go through uninstantiated quantifiers"
              in
              (tgt, subgoals, s)
          (* Exists *)
          | FBind (`Exist, x, ty, f), 1 -> begin
              match List.pop_assoc x s with
              | s, Sbound (EVar (z, _)) ->
                  let f = Form.Subst.f_apply1 (x, 0) (EVar (z, 0)) f in
                  let tgt = `H (Handle.fresh (), Proof.mk_hyp f ~src) in
                  let goal, ogoals = gen_subgoals tgt ([], goal.g_goal) [] in
                  let goal = { goal with g_env = Vars.push goal.g_env (z, (ty, None)) } in
                  (tgt, (goal, ogoals), s)
              | _ -> raise TacticNotApplicable
            end
          | _ -> raise TacticNotApplicable
        end
      in
      pbp (goal, ogoals @ new_ogoals) tgt sub s tgt' sub' s'
    in

    match (tgt, sub, s, tgt', sub', s') with
    (* Axiom *)
    | _, [], _, _, [], _ -> List.rev ogoals
    (* Right invertible rules *)
    | tgt', sub', s', `C f, i :: sub, s when invertible Pos f ->
        right_inv_rules f i sub s tgt' sub' s'
    | `C f, i :: sub, s, tgt', sub', s' when invertible Pos f ->
        right_inv_rules f i sub s tgt' sub' s'
    (* Left invertible rules *)
    | tgt', sub', s', `H (src, Proof.{ h_form = f; _ }), i :: sub, s when invertible Neg f ->
        left_inv_rules f src i sub s tgt' sub' s'
    | `H (src, Proof.{ h_form = f; _ }), i :: sub, s, tgt', sub', s' when invertible Neg f ->
        left_inv_rules f src i sub s tgt' sub' s'
    (* Right non-invertible rules *)
    | tgt', sub', s', `C f, i :: sub, s | `C f, i :: sub, s, tgt', sub', s' ->
        let tgt, (goal, new_ogoals), s =
          begin
            match (f, i + 1) with
            (* Or *)
            | FConn (`Or, [ f1; _ ]), 1 ->
                let tgt = `C f1 in
                let subgoals = gen_subgoals tgt ([], f1) [] in
                (tgt, subgoals, s)
            | FConn (`Or, [ _; f2 ]), 2 ->
                let tgt = `C f2 in
                let subgoals = gen_subgoals tgt ([], f2) [] in
                (tgt, subgoals, s)
            (* Exists *)
            | FBind (`Exist, x, _, f), 1 ->
                let s, item = List.pop_assoc x s in
                let tgt, subgoals =
                  match item with
                  | Sbound t ->
                      let f = Form.Subst.f_apply1 (x, 0) t f in
                      let tgt = `C f in
                      (tgt, gen_subgoals tgt ([], f) [])
                  | Sflex -> failwith "cannot go through uninstantiated quantifiers"
                in
                (tgt, subgoals, s)
            | _ -> raise TacticNotApplicable
          end
        in
        pbp (goal, ogoals @ new_ogoals) tgt sub s tgt' sub' s'
    (* Left non-invertible rules *)
    | tgt', sub', s', `H (src, Proof.{ h_form = f; _ }), i :: sub, s
    | `H (src, Proof.{ h_form = f; _ }), i :: sub, s, tgt', sub', s' ->
        let tgt, (goal, new_ogoals), s =
          begin
            match tgt' with
            (* Hypothesis vs. Conclusion *)
            | `C _ -> begin
                match (f, i + 1) with
                (* Imp *)
                | FConn (`Imp, [ f1; f2 ]), 2 ->
                    let tgt = `H (Handle.fresh (), Proof.mk_hyp f2 ~src) in
                    let subgoals = gen_subgoals tgt ([], goal.g_goal) [ ([], f1) ] in
                    (tgt, subgoals, s)
                | _ -> raise TacticNotApplicable
              end
            (* Hypothesis vs. Hypothesis *)
            | `H _ -> begin
                match (f, i + 1) with
                (* Imp *)
                | FConn (`Imp, [ f1; f2 ]), 1 ->
                    let tgt = `C f1 in
                    let subgoals =
                      gen_subgoals tgt ([], f1) [ ([ (Some src, [ f2 ]) ], goal.g_goal) ]
                    in
                    (tgt, subgoals, s)
                | FConn (`Imp, [ f1; f2 ]), 2 ->
                    let tgt = `H (Handle.fresh (), Proof.mk_hyp f2 ~src) in
                    let subgoals = gen_subgoals tgt ([], goal.g_goal) [ ([], f1) ] in
                    (tgt, subgoals, s)
                (* Not *)
                | FConn (`Not, [ f1 ]), 1 ->
                    let tgt = `C f1 in
                    let subgoals = gen_subgoals tgt ([], f1) [] in
                    (tgt, subgoals, s)
                | _ -> raise TacticNotApplicable
              end
            | _ -> raise TacticNotApplicable
          end
        in

        pbp (goal, ogoals @ new_ogoals) tgt sub s tgt' sub' s'
    | _ -> raise TacticNotApplicable
  in

  let subgoals = pbp (goal, []) item_src sub_src s_src item_dst sub_dst s_dst in
  snd @@ Proof.xprogress proof hd subgoals

(** [elim_units f] eliminates all occurrences of units
      in formula [f] using algebraic unit laws. *)
let rec elim_units : form -> form = function
  (* Absorbing elements *)
  | FConn (`And, [ _; FFalse ])
  | FConn (`And, [ FFalse; _ ])
  | FConn (`Not, [ FTrue ])
  | FBind (`Exist, _, _, FFalse) ->
      Form.f_false
  (* | FPred ("_EQ", [e1; e2]) when Form.e_equal e1 e2 ->
      Form.f_true *)
  | FConn (`Or, [ _; FTrue ])
  | FConn (`Or, [ FTrue; _ ])
  | FConn (`Imp, [ _; FTrue ])
  | FConn (`Imp, [ FFalse; _ ])
  | FConn (`Not, [ FFalse ])
  | FBind (`Forall, _, _, FTrue) ->
      Form.f_true
  (* Neutral elements *)
  | FConn (`And, [ f; FTrue ])
  | FConn (`And, [ FTrue; f ])
  | FConn (`Or, [ f; FFalse ])
  | FConn (`Or, [ FFalse; f ])
  | FConn (`Imp, [ FTrue; f ])
  | FConn (`Equiv, [ FTrue; f ])
  | FConn (`Equiv, [ f; FTrue ]) ->
      elim_units f
  | (FTrue | FFalse | FPred _) as f -> f
  | FConn (c, fs) as f ->
      let fs' = List.map elim_units fs in
      if fs = fs' then f else elim_units (FConn (c, fs'))
  | FBind (b, x, ty, f1) as f ->
      let f1' = elim_units f1 in
      if f1 = f1' then f else elim_units (FBind (b, x, ty, f1'))

let print_linkage env (mode : [ `Backward | `Forward ]) ((l, _), (r, _)) =
  let op = match mode with `Backward -> "⊢" | `Forward -> "∗" in
  Printf.sprintf "%s %s %s" (Notation.f_tostring env l) op (Notation.f_tostring env r)


(** [dlink] stands for _d_eep linking, and implements the deep interaction phase
      à la Chaudhuri for intuitionistic logic. *)
let dlink ((src, dst) : link) ((s_src, s_dst) : Form.Subst.subst * Form.Subst.subst)
    (proof : Proof.proof) : Proof.subgoal * itrace =
  let open Form in
  let open Subst in
  let open Proof in
  let { g_pregoal = goal; _ }, item_src, (sub_src, t_src) = of_ipath proof src in
  let _, item_dst, (sub_dst, t_dst) = of_ipath proof dst in

  begin
    match (t_src, t_dst) with `F _, `E _ | `E _, `F _ -> raise TacticNotApplicable | _ -> ()
  end;

  (* [well_scoped lenv e] returns [true] if all variables in the
     expression [e] are bound either in the global environment [goal.g_env],
     or in the local environment [lenv]. *)
  let well_scoped ctx e =
    e_vars e
    |> List.for_all
         begin
           fun x -> fc_is_bound x ctx || Vars.exists goal.g_env (fc_exit x ctx)
         end
  in

  (* [instantiable lenv ctx s x] returns [true] if the variable [x] is
     either flex, or bound in substitution [s] to an expression [e] which is
     well-scoped. *)
  let instantiable lenv ctx s x ty =
    let lenv = LEnv.enter lenv x ty in
    match get_tag (x, LEnv.get_index lenv x) s with
    | Some (Sbound e) -> well_scoped ctx e
    | Some Sflex -> true
    | None -> false
  in

  let invertible (kind : [ `Left | `Right | `Forward ]) (f : form) : bool =
    match kind with
    (* Right invertible *)
    | `Right -> begin
        match f with
        | FConn (c, _) -> begin match c with `Imp | `Not | `Equiv -> true | _ -> false end
        | FBind (`Forall, _, _, _) -> true
        | _ -> false
      end
    (* Left invertible *)
    | `Left -> begin
        match f with
        | FConn (c, _) -> begin match c with `Or -> true | _ -> false end
        | FBind (`Exist, _, _, _) -> true
        | _ -> false
      end
    (* Forward invertible *)
    | `Forward -> begin
        match f with
        | FConn (c, _) -> begin match c with _ -> false end
        | FBind (`Exist, _, _, _) -> true
        | _ -> false
      end
  in

  let no_prio kind ((f, sub) : form * int list) =
    let inv = invertible kind f in
    (not inv) || List.is_empty sub
  in

  let backward_core (ctx : fctx) (itrace : itrace) 
    (s : ((LEnv.lenv * subst) * (LEnv.lenv * subst)) ref)
    (switch_pol : bool ref)
    ((((l, lsub) as h), ((r, rsub) as c)) as linkage : (form * int list) * (form * int list))
    =
    let ((env1, s1) as es1), ((env2, s2) as es2) = !s in
    begin match linkage with
    (* Right rules *)

      (* R∧s *)
      | _, (FConn (`And, fs), i :: sub) when no_prio `Left h -> begin
          try
            let fi, fs = List.pop_at i fs in
            (Some (CConn (`And, fs, i)), (1, None), (h, (fi, sub)))
          with Not_found -> failwith "empty conjunction"
        end
      (* R∨ *)
      | _, (FConn (`Or, fs), i :: sub) when no_prio `Left h -> begin
          try
            let fi, fs = List.pop_at i fs in
            (Some (CConn (`Or, fs, i)), (1, None), (h, (fi, sub)))
          with Not_found -> failwith "empty disjunction"
        end
      (* R⇒₁ *)
      | _, (FConn (`Imp, [ f1; f2 ]), 0 :: sub) ->
          switch_pol := true;
          (Some (CConn (`Imp, [ f2 ], 0)), (1, None), (h, (f1, sub)))
      (* R⇒₂ *)
      | _, (FConn (`Imp, [ f1; f2 ]), 1 :: sub) ->
          (Some (CConn (`Imp, [ f1 ], 1)), (1, None), (h, (f2, sub)))
      (* R¬ *)
      | _, (FConn (`Not, [ f1 ]), 0 :: sub) ->
          switch_pol := true;
          (Some (CConn (`Not, [], 0)), (1, None), (h, (f1, sub)))
      | _, (FConn (`Equiv, [ _; _ ]), _) ->
          failwith "DnD on positive equivalence currently unsupported"
      | _, (FBind (`Exist, x, ty, f1), 0 :: sub)
        when no_prio `Left h && instantiable env2 ctx s2 x ty ->
          let env2 = LEnv.enter env2 x ty in
          s := (es1, (env2, s2));
          begin
            match get_tag (x, LEnv.get_index env2 x) s2 with
            (* R∃i *)
            | Some (Sbound e) ->
                let f1 = Subst.f_apply1 (x, 0) e f1 in
                (None, (1, Some (env1, env2, e)), (h, (f1, sub)))
            (* R∃s *)
            | Some Sflex ->
                s := (es1, (env2, s2));
                let h = (f_shift (x, 0) l, lsub) in
                (Some (CBind (`Exist, x, ty)), (1, None), (h, (f1, sub)))
            | None -> assert false
          end
    (* R∀s *)
    | _, (FBind (`Forall, x, ty, f1), 0 :: sub) ->
        s := (es1, (LEnv.enter env2 x ty, s2));
        let h = (f_shift (x, 0) l, lsub) in
        (Some (CBind (`Forall, x, ty)), (1, None), (h, (f1, sub)))
    (* Left rules *)
      (* L∧ *)
      | (FConn (`And, fs), i :: sub), _ when no_prio `Right c -> begin
          try (None, (0, None), ((List.at fs i, sub), c))
          with Invalid_argument _ -> failwith "empty conjunction"
        end
      (* L∨ *)
      | (FConn (`Or, fs), i :: sub), _ -> begin
          try
            let fi, fs = List.pop_at i fs in
            let fs = List.map (fun fj -> f_imp fj r) fs in
            (Some (CConn (`And, fs, i)), (0, None), ((fi, sub), c))
          with Not_found -> failwith "empty disjunction"
        end
      (* L⇒₂ *)
      | (FConn (`Imp, [ f1; f2 ]), 1 :: sub), _ when no_prio `Right c ->
          js_log "L⇒₂\n";
          (Some (CConn (`And, [ f1 ], 1)), (0, None), ((f2, sub), c))
      (* L⇔₁ *)
      | (FConn (`Equiv, [ f1; f2 ]), 0 :: sub), _ when no_prio `Right c ->
          (Some (CConn (`And, [ f2 ], 0)), (0, None), ((f1, sub), c))
      (* L⇔₂ *)
      | (FConn (`Equiv, [ f1; f2 ]), 1 :: sub), _ when no_prio `Right c ->
          (Some (CConn (`And, [ f1 ], 1)), (0, None), ((f2, sub), c))
      (* L∃s *)
      | (FBind (`Exist, x, ty, f1), 0 :: sub), _ ->
          s := ((LEnv.enter env1 x ty, s1), es2);
          let c = (f_shift (x, 0) r, rsub) in
          (Some (CBind (`Forall, x, ty)), (0, None), ((f1, sub), c))
      | (FBind (`Forall, x, ty, f1), 0 :: sub), _
        when no_prio `Right c && instantiable env1 ctx s1 x ty ->
          let env1 = LEnv.enter env1 x ty in
          s := ((env1, s1), es2);
          begin
            match get_tag (x, LEnv.get_index env1 x) s1 with
            (* L∀i *)
            | Some (Sbound e) ->
                let f1 = f_apply1 (x, 0) e f1 in
                (None, (0, Some (env1, env2, e)), ((f1, sub), c))
            (* L∀s *)
            | Some Sflex ->
                s := ((env1, s1), es2);
                let c = (f_shift (x, 0) r, rsub) in
                (Some (CBind (`Exist, x, ty)), (0, None), ((f1, sub), c))
            | None -> assert false
          end
    | _ ->
        js_log "No backward rule matched\n";
        raise TacticNotApplicable
    end
  in

  let rec backward (ctx : fctx) (itrace : itrace)
      ((((env1, s1) as es1), ((env2, s2) as es2)) as s : (LEnv.lenv * subst) * (LEnv.lenv * subst))
      ((((l, lsub) as h), ((r, rsub) as c)) as linkage : (form * int list) * (form * int list)) :
      form * itrace =
    (* js_log (Subst.to_string s1 ^ " ⊢ " ^ Subst.to_string s2); *)
    js_log (print_linkage goal.g_env `Backward linkage);

    match linkage with
    (* End rules *)
    | (_, []), (_, []) ->
        let f =
          begin
            match (l, r) with
            (* Bid *)
            | _ when f_equal goal.g_env l r -> f_true
            | FPred (c1, ts1), FPred (c2, ts2) when c1 = c2 ->
                List.fold_left2 (fun f t1 t2 -> f_and f (FPred ("_EQ", [ t1; t2 ]))) f_true ts1 ts2
            (* Brel *)
            | _ -> f_imp l r
          end
        in
        (fc_fill f (fc_rev ctx), itrace)
    | (FPred ("_EQ", [ e1; e2 ]), [ i ]), (FPred _, _)
      when e_equal_delta goal.g_env (subexpr (`F r) rsub) (if i = 0 then e1 else e2) ->
        let res =
          (* L=₁ *)
          if i = 0 then e2 (* L=₂ *) else e1
        in
        let f = rewrite_subterm (`E res) (`F r) rsub |> form_of_term in
        (fc_fill f (fc_rev ctx), itrace)
    (* Commuting rules *)
    | _ ->
        let switch_pol = ref false in
        let s = ref s in

        let ( (ictx : ifctx option)
            , (choice : choice)
            , (linkage : (form * int list) * (form * int list)) ) =
          backward_core ctx itrace s switch_pol linkage
        in
        js_log "Finished matching\n";
        let cont = if !switch_pol then forward ~side:1 else backward in
        let ctx = match ictx with Some i -> i :: ctx | None -> ctx in
        cont ctx (choice :: itrace) !s linkage
  and forward (ctx : fctx) (itrace : itrace) ?(side = 1)
      ((((env1, _) as es1), ((env2, s2) as es2)) as s : (LEnv.lenv * subst) * (LEnv.lenv * subst))
      ((((l, lsub) as h), (r, rsub)) as linkage : (form * int list) * (form * int list)) :
      form * itrace =
    js_log (print_linkage goal.g_env `Forward linkage);

    match linkage with
    (* End rules *)
    | (_, []), (_, []) ->
        let f =
          begin
            match (l, r) with
            (* Fid *)
            | _ when f_equal goal.g_env l r -> l
            (* Frel *)
            | _ -> f_and l r
          end
        in
        (fc_fill f (fc_rev ctx), itrace)
    | (FPred ("_EQ", [ e1; e2 ]), [ i ]), (FPred _, _)
      when e_equal_delta goal.g_env (subexpr (`F r) rsub) (if i = 0 then e1 else e2) ->
        let res =
          (* L=₁ *)
          if i = 0 then e2 (* L=₂ *) else e1
        in
        let f = rewrite_subterm (`E res) (`F r) rsub |> form_of_term in
        (fc_fill f (fc_rev ctx), itrace)
    (* Commuting rules *)
    | _ ->
        let switch_pol = ref false in
        let s = ref s in
        let new_side = ref side in
        let witness = ref None in

        let (ictx : ifctx option), (linkage : (form * int list) * (form * int list)) =
          begin
            match linkage with
            (* F∧ *)
            | _, (FConn (`And, fs), i :: sub) -> begin
                try (None, (h, (List.at fs i, sub)))
                with Not_found -> failwith "empty conjunction"
              end
            (* F∨ *)
            | _, (FConn (`Or, fs), i :: sub) when no_prio `Forward h -> begin
                try
                  let fi, fs = List.pop_at i fs in
                  (Some (CConn (`Or, fs, i)), (h, (fi, sub)))
                with Not_found -> failwith "empty disjunction"
              end
            (* F⇒₁ *)
            | _, (FConn (`Imp, [ f1; f2 ]), 0 :: sub) when no_prio `Forward h ->
                switch_pol := true;
                (Some (CConn (`Imp, [ f2 ], 0)), (h, (f1, sub)))
            (* F⇒₂ *)
            | _, (FConn (`Imp, [ f1; f2 ]), 1 :: sub) when no_prio `Forward h ->
                (Some (CConn (`Imp, [ f1 ], 1)), (h, (f2, sub)))
            (* F¬ *)
            | _, (FConn (`Not, [ f1 ]), 0 :: sub) when no_prio `Forward h ->
                switch_pol := true;
                (Some (CConn (`Not, [], 0)), (h, (f1, sub)))
            (* F⇔₁ *)
            | _, (FConn (`Equiv, [ f1; f2 ]), 0 :: sub) when no_prio `Forward h ->
                switch_pol := true;
                (Some (CConn (`Imp, [ f2 ], 0)), (h, (f1, sub)))
            (* F⇔₂ *)
            | _, (FConn (`Equiv, [ f1; f2 ]), 1 :: sub) when no_prio `Forward h ->
                switch_pol := true;
                (Some (CConn (`Imp, [ f1 ], 0)), (h, (f2, sub)))
            (* F∃s *)
            | _, (FBind (`Exist, x, ty, f1), 0 :: sub) ->
                s := (es1, (LEnv.enter env2 x ty, s2));
                let h = (f_shift (x, 0) l, lsub) in
                (Some (CBind (`Exist, x, ty)), (h, (f1, sub)))
            | _, (FBind (`Forall, x, ty, f1), 0 :: sub)
              when no_prio `Forward h && instantiable env2 ctx s2 x ty ->
                let env2 = LEnv.enter env2 x ty in
                s := (es1, (env2, s2));
                begin
                  match get_tag (x, LEnv.get_index env2 x) s2 with
                  (* F∀i *)
                  | Some (Sbound e) ->
                      let f1 = Subst.f_apply1 (x, 0) e f1 in
                      witness := if side = 1 then Some (env1, env2, e) else Some (env2, env1, e);
                      (None, (h, (f1, sub)))
                  (* F∀s *)
                  | Some Sflex ->
                      s := (es1, (LEnv.enter env2 x ty, s2));
                      let h = (f_shift (x, 0) l, lsub) in
                      (Some (CBind (`Forall, x, ty)), (h, (f1, sub)))
                  | None -> assert false
                end
            (* Fcomm *)
            | h, h' ->
                s := (es2, es1);
                new_side := 1 - side;
                (None, (h', h))
          end
        in
        let cont = if !switch_pol then backward else forward ~side:!new_side in
        let ctx = match ictx with Some i -> i :: ctx | None -> ctx in
        let itrace = if !new_side <> side then itrace else (!new_side, !witness) :: itrace in
        cont ctx itrace !s linkage
  in

  let subgoal, itrace =
    match ((item_src, sub_src, s_src), (item_dst, sub_dst, s_dst)) with
    | (`H (hid, { h_form = h; _ }), subh, sh), (`C c, subc, sc)
    | (`C c, subc, sc), (`H (hid, { h_form = h; _ }), subh, sh) ->
        let form, itrace =
          backward [] [] ((LEnv.empty, sh), (LEnv.empty, sc)) ((h, subh), (c, subc))
        in
        (([ (Some hid, []) ], form |> elim_units), itrace)
    | (`H (hid, { h_form = h; _ }), subh, s), (`H (hid', { h_form = h'; _ }), subh', s') ->
        let form, itrace =
          forward [] [] ((LEnv.empty, s), (LEnv.empty, s')) ((h, subh), (h', subh'))
        in
        (([ (Some hid, []); (Some hid', [ form |> elim_units ]) ], goal.g_goal), itrace)
    | _ -> raise TacticNotApplicable
  in
  let itrace = List.rev itrace in

  (subgoal, itrace)

(* -------------------------------------------------------------------- *)
(* Logical actions *)

type linkaction =
  [ `Nothing
  | `Both of linkaction * linkaction
  | `Subform of Form.Subst.subst * Form.Subst.subst
  | `Instantiate of expr * ipath
  | `Rewrite of expr * expr * ipath list
  | `Fold of vname * ipath list
  | `Unfold of vname * ipath list ]

let remove_nothing =
  let rec doit = function
    | [] -> []
    | a :: l -> (
        match a with
        | `Nothing -> doit l
        | `Both (a, a') -> begin
            match doit [ a; a' ] with
            | [] -> doit l
            | [ a ] -> a :: doit l
            | [ a; a' ] -> `Both (a, a') :: doit l
            | _ -> assert false
          end
        | _ -> a :: doit l)
  in
  doit

let string_of_linkaction proof =
  let rec doit = function
    | `Nothing -> "⊥"
    | `Both (a, a') -> Printf.sprintf "(%s, %s)" (doit a) (doit a')
    | `Subform _ -> "SFL"
    | `Instantiate _ -> "Instantiate"
    | `Rewrite (red, res, tgts) ->
        Printf.sprintf "%s[%s ~> %s]"
          (List.to_string ~sep:", " ~left:"{" ~right:"}"
             (fun p ->
               let Proof.{ g_pregoal; _ }, _, (_, t) = of_ipath proof p in
               Notation.tostring g_pregoal.g_env t)
             tgts)
          red res
  in
  doit

type action_type =
  [ `Intro of int
  | `Elim of Handle.t * int
  | `Lemma of name
  | `Ind of Handle.t
  | `Simpl of ipath
  | `Red of ipath
  | `Indt of ipath
  | `Case of ipath
  | `Pbp of ipath
  | `Fold of vname
  | `Unfold of vname
  | `Hyperlink of hyperlink * linkaction list ]

type action = Handle.t * action_type

(* -------------------------------------------------------------------- *)
(* (Hyper)link search (for highlighting) *)

(** [t_subs f] returns all the paths leading to a subterm in [t]. *)
let t_subs (t : term) : int list list =
  let rec aux sub = function
    | `E (EFun (_, es)) | `F (FPred (_, es)) ->
        es
        |> List.mapi (fun i e ->
               let sub = sub @ [ i ] in
               sub :: aux sub (`E e))
        |> List.concat
    | `F (FConn (_, fs)) ->
        fs
        |> List.mapi (fun i f ->
               let sub = sub @ [ i ] in
               sub :: aux sub (`F f))
        |> List.concat
    | `F (FBind (_, _, _, f)) ->
        let sub = sub @ [ 0 ] in
        sub :: aux sub (`F f)
    | _ -> []
  in

  [] :: aux [] t

(** [f_subs f] returns all the paths leading to a subformula in [f]. *)
let f_subs (f : form) : int list list =
  let rec aux sub = function
    | FConn (_, fs) ->
        fs
        |> List.mapi (fun i f ->
               let sub = sub @ [ i ] in
               sub :: aux sub f)
        |> List.concat
    | FBind (_, _, _, f) ->
        let sub = sub @ [ 0 ] in
        sub :: aux sub f
    | _ -> []
  in

  [] :: aux [] f

(** [e_subs f] returns all the paths leading to a subexpression in [f]. *)
let e_subs (f : form) : int list list =
  let rec f_aux sub = function
    | FPred (_, es) ->
        es
        |> List.mapi (fun i e ->
               let sub = sub @ [ i ] in
               sub :: e_aux sub e)
        |> List.concat
    | FConn (_, fs) -> fs |> List.mapi (fun i f -> f_aux (sub @ [ i ]) f) |> List.concat
    | FBind (_, _, _, f) -> f_aux (sub @ [ 0 ]) f
    | _ -> []
  and e_aux sub = function
    | EVar _ -> []
    | EFun (_, es) ->
        es
        |> List.mapi (fun i e ->
               let sub = sub @ [ i ] in
               sub :: e_aux sub e)
        |> List.concat
  in

  f_aux [] f

(** The type of hyperlink predicates [hlpred] captures functions which
      map a hyperlink in a proof to a list of possible link actions.

      One can emulate a traditional boolean predicate by returning the singleton
      [`Nothing] to indicate membership, or the empty list to indicate absence
      thereof. *)

type lpred = Proof.proof -> link -> linkaction list
type hlpred = Proof.proof -> hyperlink -> linkaction list

let hlpred_of_lpred : lpred -> hlpred =
 fun p pr -> function [ src ], [ dst ] -> p pr (src, dst) | _ -> []

(** [hlpred_mult lps] returns a hyperlink predicate that denotes the cartesian
      product of the actions denoted by the hyperlink predicates in [lps]. *)
let hlpred_mult : hlpred list -> hlpred =
  let mult : hlpred -> hlpred -> hlpred =
   fun p1 p2 pr lnk ->
    List.cartesian_product (p1 pr lnk) (p2 pr lnk) |> List.map (fun (a1, a2) -> `Both (a1, a2))
  in
  List.fold_left mult (fun _ _ -> [ `Nothing ])

(** [hlpred_add lps] returns a hyperlink predicate that denotes the disjoint
      union of the actions denoted by the hyperlink predicates in [lps]. *)
let hlpred_add : hlpred list -> hlpred =
 fun ps pr lnk -> List.map (fun p -> p pr lnk) ps |> List.concat

(** [hlpred_if_empty p1 p2] is equivalent to [p1] at links where the
      latter is non-empty, and [p2] elsewhere. *)
let hlpred_if_empty : hlpred -> hlpred -> hlpred =
 fun p1 p2 pr lnk ->
  let actions = p1 pr lnk in
  if not (List.is_empty actions) then actions else p2 pr lnk

(** [search_linkactions hlp proof (src, dst)] returns all links between
      subterms of [src] and [dst] in [proof] that can interact according to
      the hyperlink predicate [hlp], together with the lists of possible link
      actions determined by the predicate.

      If [fixed_srcs] (resp. [fixed_dsts]) is set, the function returns only
      hyperlinks with sources [fixed_srcs] (resp. destinations [fixed_dsts]),
      and whose destinations (resp. sources) are subterms of [dst] (resp.
      [src]). *)
let search_linkactions ?(fixed_srcs : ipath list option) ?(fixed_dsts : ipath list option)
    (hlp : hlpred) proof ((src, dst) : link) : (hyperlink * linkaction list) list =
  let subpath p sub = { root = p.root; ctxt = p.ctxt; sub = p.sub @ sub } in

  let query_actions lnk =
    match hlp proof lnk with _ :: _ as actions -> [ (lnk, actions) ] | [] -> []
  in

  let open Monad.List in
  match (fixed_srcs, fixed_dsts) with
  | Some srcs, Some dsts -> query_actions (srcs, dsts)
  | Some srcs, None ->
      let _, _, (_, t_dst) = of_ipath proof dst in
      t_subs t_dst >>= fun sub_dst -> query_actions (srcs, [ subpath dst sub_dst ])
  | None, Some dsts ->
      let _, _, (_, t_src) = of_ipath proof src in
      t_subs t_src >>= fun sub_src -> query_actions ([ subpath src sub_src ], dsts)
  | None, None ->
      let _, _, (_, t_src) = of_ipath proof src in
      let _, _, (_, t_dst) = of_ipath proof dst in
      t_subs t_src >>= fun sub_src ->
      t_subs t_dst >>= fun sub_dst ->
      query_actions ([ subpath src sub_src ], [ subpath dst sub_dst ])

module PreUnif = struct
  open Form

  module Deps = struct
    include Graph.Persistent.Digraph.Concrete (Name)

    let subst (deps : t) (s : Subst.subst) : t =
      (* For each item [x := e] in the substitution *)
      Subst.fold
        begin
          fun deps (x, tag) ->
            let fvs = match tag with Sbound e -> e_vars e | Sflex -> [] in
            (* For each variable [y] depending on [x] *)
            try
              fold_succ
                begin
                  fun y deps ->
                    (* For each variable [z] occurring in [e] *)
                    List.fold_left
                      begin
                        fun deps (z, _) ->
                          (* Add an edge stating that [y] depends on [z] *)
                          add_edge deps z y
                      end
                      deps fvs
                end
                deps x deps
            with Invalid_argument _ -> deps
        end
        deps s
  end

  module TraverseDeps = Graph.Traverse.Dfs (Deps)

  let acyclic = not <<| TraverseDeps.has_cycle

  module Env = struct
    (** While traversing formulas in search for targets to unify, we need to
          record and update multiple informations handling the first-order content
          of the proof. We do so with a record of the form
           
            [{deps; rnm; subst}]
           
          where:

          - [deps] is a directed graph recording the dependency relation between
            existential and eigenvariables, in the same spirit of the dependency
            relation of expansion trees.
 
          - [rnm] is an association list, where each item [(z, x)] maps a fresh name
            [z] to the variable [x] it renames. Indeed, to avoid name clashes between
            bound variables of [f1] and [f2] during unification, we give them temporary
            fresh names, which are reverted to the original names with [rnm] when
            producing the final substitution for each formula.
           
          - [subst] is the substitution that will be fed to unification, in which we
            record existential variables in [Sflex] entries.
      *)
    type t = { deps : Deps.t; rnm : (name * name) list; subst : Subst.subst }
  end

  module State = Monad.State (Env)

  let traverse (p, t) i : (pol * term) State.t =
    let open State in
    match (p, t) with
    | Pos, `F (FBind (`Forall, x, _, f)) | Neg, `F (FBind (`Exist, x, _, f)) ->
        get >>= fun { deps; rnm; subst } ->
        let z = EVars.fresh () in
        let exs = Subst.fold (fun acc (x, t) -> if t = Sflex then x :: acc else acc) [] subst in
        let deps = List.fold_left (fun deps y -> Deps.add_edge deps y z) deps exs in
        let rnm = (z, x) :: rnm in
        put { deps; rnm; subst } >>= fun _ ->
        let f = Form.Subst.f_apply1 (x, 0) (EVar (z, 0)) f in
        return (p, `F f)
    | Neg, `F (FBind (`Forall, x, _, f)) | Pos, `F (FBind (`Exist, x, _, f)) ->
        get >>= fun ({ rnm; subst; _ } as st) ->
        let z = EVars.fresh () in
        let rnm = (z, x) :: rnm in
        let subst = Subst.push z Sflex subst in
        put { st with rnm; subst } >>= fun _ ->
        let f = Form.Subst.f_apply1 (x, 0) (EVar (z, 0)) f in
        return (p, `F f)
    | _ -> return (direct_subterm_pol (p, t) i)

  let traverse = State.fold traverse
end

(** [wf_subform_link proof (src, dst)] checks if [src] and [dst] lead to
      unifiable subformulas of opposite polarities in the focused goal of
      [proof], and returns the associated substitutions if they do inside a
      [`Subform] link action.
      
      If [drewrite] is set to [true], it only checks for deep rewrite links,
      that is links where one side is a negative equality operand, and the other
      side an arbitrary unifiable subexpression of the same type. *)
let wf_subform_link ?(drewrite = false) : lpred =
  let open Form in
  let open PreUnif in
  let is_eq_operand proof (p : ipath) =
    try
      let eq_sub = List.(remove_at (length p.sub - 1) p.sub) in
      let eq_path = { p with sub = eq_sub } in
      let _, _, (_, t) = of_ipath proof eq_path in
      match t with `F (FPred ("_EQ", _)) -> true | _ -> false
    with Invalid_argument _ -> false
  in

  fun proof (src, dst) ->
    let goal, item_src, (sub_src, t_src) = of_ipath proof src in
    let _, item_dst, (sub_dst, t_dst) = of_ipath proof dst in

    try
      let f1, f2 = pair_map form_of_item (item_src, item_dst) in

      let p1 = pol_of_item item_src in
      let p2 = pol_of_item item_dst in

      let sub1 = sub_src in
      let sub2 = sub_dst in

      let deps, sp1, st1, rnm1, s1, sp2, st2, rnm2, s2 =
        let open State in
        run
          begin
            traverse (p1, `F f1) sub1 >>= fun (sp1, sf1) ->
            get >>= fun st1 ->
            put { st1 with rnm = []; subst = Subst.empty } >>= fun _ ->
            traverse (p2, `F f2) sub2 >>= fun (sp2, sf2) ->
            get >>= fun st2 ->
            return (st2.deps, sp1, sf1, st1.rnm, st1.subst, sp2, sf2, st2.rnm, st2.subst)
          end
          { deps = Deps.empty; rnm = []; subst = Subst.empty }
      in

      let s1 = Subst.aslist s1 in
      let s2 = Subst.aslist s2 in
      let s = Subst.oflist (s1 @ s2) in

      let s =
        begin
          match (st1, st2) with
          (* Subformula linking *)
          | `F f1, `F f2 when not drewrite -> begin
              match (sp1, sp2) with
              | Pos, Neg | Neg, Pos | Sup, _ | _, Sup ->
                  f_unify goal.g_pregoal.g_env LEnv.empty s [ (f1, f2) ]
              | _ -> None
            end
          (* Deep rewrite *)
          | `E e1, `E e2
            when drewrite
                 &&
                 let env = goal.g_pregoal.g_env in
                 let ty1 = einfer (env_of_ipath proof src) (expr_of_term t_src) in
                 let ty2 = einfer (env_of_ipath proof dst) (expr_of_term t_dst) in
                 Form.(t_equal env ty1 ty2) ->
              let eq1, eq2 = pair_map (is_eq_operand proof) (src, dst) in
              begin
                match ((sp1, eq1), (sp2, eq2)) with
                | (Neg, true), _ | _, (Neg, true) ->
                    e_unify goal.g_pregoal.g_env LEnv.empty s [ (e1, e2) ]
                | _ -> None
              end
          | _ -> None
        end
      in

      match s with
      | Some s when acyclic (Deps.subst deps s) ->
          let s1, s2 = List.split_at (List.length s1) (Subst.aslist s) in

          let rename rnm1 rnm2 =
            List.map
              begin
                fun (x, tag) ->
                  let get_name x rnm = Option.default x (List.assoc_opt x rnm) in
                  let x = get_name x rnm1 in
                  let tag =
                    let rec rename = function
                      | EVar (x, i) -> EVar (get_name x rnm2, i)
                      | EFun (f, es) -> EFun (f, List.map rename es)
                    in
                    match tag with Sbound e -> Sbound (rename e) | _ -> tag
                  in
                  (x, tag)
              end
          in

          let s1 = s1 |> rename rnm1 rnm2 |> List.rev |> Subst.oflist in
          let s2 = s2 |> rename rnm2 rnm1 |> List.rev |> Subst.oflist in

          [ `Subform (s1, s2) ]
      | _ -> []
    with Invalid_argument _ -> []

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
    | `H _ -> n + 1
    | `V _ -> raise (Invalid_argument "Expected a formula item")
  in

  try
    match (neg_count src, neg_count dst) with
    | m, n when (m > 0 && n > 0) || (m = 0 && n <= 1) || (m <= 1 && n = 0) -> [ `Nothing ]
    | _ -> []
  with InvalidSubFormPath _ | Invalid_argument _ -> []

(** [instantiate_link proof (srcs, dsts)] checks if [srcs] (resp.
      [dsts]) leads to an expression, and [dsts] (resp. [srcs]) leads either to
      an instantiable quantified subformula, or the set of occurrences of an
      instantiable quantified variable. It it succeeds, it returns the
      corresponding [`Instantiate] link action. *)
let instantiate_link : hlpred =
  let is_free_expr (t : term) (sub : int list) : bool =
    let lenv, subt =
      List.fold_left
        (fun (lenv, t) i ->
          let lenv = match t with `F (FBind (_, x, ty, _)) -> LEnv.enter lenv x ty | _ -> lenv in
          let t = direct_subterm t i in
          (lenv, t))
        (LEnv.empty, t) sub
    in
    match subt with `F _ -> false | `E e -> List.for_all (not <<| LEnv.exists lenv) (e_vars e)
  in

  fun proof (srcs, dsts) ->
    (* Link to quantified subformula *)
    let to_form p_wit p_form =
      let Proof.{ g_pregoal = goal; _ }, item_wit, (sub_wit, wit) = of_ipath proof p_wit in

      let where = match p_wit.ctxt.kind with `Var w -> w | _ -> `Body in
      let ctxt_wit = term_of_item ~where item_wit in

      (* Check that the witness contains only free variables *)
      if is_free_expr ctxt_wit sub_wit
      then
        let pol = pol_of_ipath proof p_form in
        let f = term_of_ipath proof p_form in

        let wit = expr_of_term wit in
        let ty_wit = Form.einfer goal.g_env wit in

        (* Check that the quantifier is instantiable, meaning it has
           the right polarity as well as the same type as the witness *)
        match (pol, f) with
        | (Neg, `F (FBind (`Forall, _, ty, _)) | Pos, `F (FBind (`Exist, _, ty, _)))
          when Form.t_equal goal.g_env ty ty_wit ->
            [ `Instantiate (wit, p_form) ]
        | _ -> []
      else []
    in

    (* Link to quantified occurrences *)
    match (srcs, dsts) with
    | [ src ], [ dst ] -> begin
        match pair_map (term_of_ipath proof) (src, dst) with
        | `E _, `F _ -> to_form src dst
        | `F _, `E _ -> to_form dst src
        | `E _, `E _ -> [] (* TODO *)
        | _ -> []
      end
    | _ -> []

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
    if p.ctxt.kind = `Hyp
    then
      let _, it, _ = of_ipath proof p in
      match (p.sub, form_of_item it) with
      | [ 0 ], FPred ("_EQ", [ red; res ]) | [ 1 ], FPred ("_EQ", [ res; red ]) -> Some (red, res)
      | _ -> None
    else None
  in

  try
    match (lnk, pair_map (List.hd |>> rewrite_data) lnk) with
    (* If it is a simple link where both ends are sides of equalities,
       disambiguate by rewriting into the destination *)
    | ([ _ ], [ dst ]), (Some (red, res), Some _) -> [ `Rewrite (red, res, [ dst ]) ]
    | ([ _ ], tgts), (Some (red, res), _) | (tgts, [ _ ]), (_, Some (red, res)) ->
        if List.exists (fun p -> p.ctxt.kind = `Var `Head) tgts
        then []
        else [ `Rewrite (red, res, tgts) ]
    | _ -> []
    (* Empty link end *)
  with Failure _ -> []

(** [fold_link lnk] checks if [lnk] is a fold hyperlink. That is, one
      end of the link is the head [x] (resp. body [e]) of a local variable
      definition, and the other end a non-empty set of arbitrary subterms where
      all occurrences of [x] (resp. [e]) are to be rewritten into [e] (resp.
      [x]).

      If the check succeeds, it returns either a [`Fold] or [`Unfold] link action.
      *)
let fold_link : hlpred =
 fun proof lnk ->
  let fold_data (p : ipath) =
    let _, it, _ = of_ipath proof p in
    match (it, p.ctxt.kind, p.sub) with
    | `V (x, (_, Some _)), `Var where, [] -> Some (x, where)
    | _ -> None
  in

  try
    match (lnk, pair_map (List.hd |>> fold_data) lnk) with
    (* If it is a simple link where both ends are variable bodies,
       disambiguate by folding in the destination *)
    | ([ _ ], [ dst ]), (Some (x, `Body), Some (_, `Body)) -> [ `Fold (x, [ dst ]) ]
    | ([ p ], tgts), (Some (x, where), _) | (tgts, [ p ]), (_, Some (x, where)) ->
        let is_head p = p.ctxt.kind = `Var `Head in
        if where = `Head
        then if List.exists is_head tgts then [] else [ `Unfold (x, tgts) ]
        else begin
          match List.filter is_head tgts with
          | [ p' ] ->
              Option.map_default
                (fun (y, _) -> [ `Unfold (y, p :: List.remove tgts p') ])
                [] (fold_data p')
          | [] -> [ `Fold (x, tgts) ]
          | _ :: _ :: _ -> []
        end
    | _ -> []
    (* Empty link end *)
  with Failure _ -> []

(* -------------------------------------------------------------------- *)
(** Graphical actions *)

type asource = { kind : asource_kind; selection : selection }
and asource_kind = [ `Click of ipath | `DnD of adnd | `Ctxt ]
and adnd = { source : ipath; destination : ipath option }
and selection = ipath list

type osource = [ `Click of ipath | `DnD of link | `Ctxt ]

let filter_db_by_name pattern proof =
  let new_db =
    proof |> Proof.get_db
    |> LemmaDB.filter
         begin
           fun name _stmt ->
             (* Check that the pattern is an exact substring of the lemma's name.
                The test is case-insensitive. *)
             let name = String.lowercase name in
             let pattern = String.lowercase pattern in
             try
               ignore (String.find name pattern);
               true
             with Not_found -> false
         end
  in
  Proof.set_db proof new_db

let filter_db_by_selection selection proof =
  (* Construct a hyperlink predicate to allow only valid linkactions. *)
  let filter =
    hlpred_add
      [ hlpred_mult (List.map hlpred_of_lpred [ wf_subform_link; intuitionistic_link ])
      ; hlpred_of_lpred @@ wf_subform_link ~drewrite:true
      ]
  in
  (* Filter the lemma database. *)
  let new_db =
    proof |> Proof.get_db
    |> LemmaDB.filter
         begin
           fun _name stmt ->
             (* Make a new goal that has :
                - the lemma as a local hypothesis.
                - its environment extended with the environment of the lemma database. *)
             let Proof.{ g_id; g_pregoal = sub } = goal_of_ipath proof selection in
             let hd = Handle.fresh () in
             let sub =
               let hyp = Proof.mk_hyp stmt in
               let g_hyps = Proof.Hyps.add sub.g_hyps hd hyp in
               let g_env = Env.union (proof |> Proof.get_db |> LemmaDB.env) sub.g_env in
               Proof.{ sub with g_hyps; g_env }
             in
             (* Replace the current goal by the new goal. *)
             let g_ids, proof = Proof.xprogress proof g_id [ sub ] in
             let g_id = List.hd g_ids in
             (* Create a path to the root of the new hypothesis (representing the lemma). *)
             let lemma_path =
               mk_ipath ~ctxt:{ kind = `Hyp; handle = Handle.toint hd } (Handle.toint g_id)
             in
             (* Make sure the path to the selection is in the new goal. *)
             let selection = mk_ipath ~ctxt:selection.ctxt ~sub:selection.sub (Handle.toint g_id) in
             (* Compute all linkactions. *)
             let linkactions =
               (* Here the source of the linkaction is fixed to the selection (no subterms),
                  but the destination is not fixed (we consider all subterms of the lemma). *)
               search_linkactions filter proof ~fixed_srcs:[ selection ]
                 (mk_ipath (Handle.toint g_id), lemma_path)
             in
             not @@ List.is_empty linkactions
         end
    (* Note that the proof is modified in the predicate of LemmaDB.filter (we add a new hypothesis),
       but since it is an immutable structure the changes are not reflected here. *)
  in
  Proof.set_db proof new_db

type aoutput =
  { description : string
  ; icon : string option
  ; highlights : ipath list
  ; kind : osource
  ; action : action
  }

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
let dnd_actions ((dnd, selection) : adnd * selection) (proof : Proof.proof) : aoutput list =
  let (Proof.{ g_id; _ } as goal) = goal_of_ipath proof dnd.source in

  let srcsel : selection = List.filter (is_sub_path dnd.source) selection in

  let dstsel : selection =
    List.remove_if (fun p -> p.ctxt.handle = dnd.source.ctxt.handle) selection
  in

  let hlpred_only_sel (p : hlpred) : hlpred =
   fun pr lnk -> if lnk = (srcsel, dstsel) then p pr lnk else []
  in

  let hlp =
    hlpred_add
      [ hlpred_mult (List.map hlpred_of_lpred [ wf_subform_link; intuitionistic_link ])
      ; hlpred_if_empty
          (wf_subform_link ~drewrite:true |> hlpred_of_lpred)
          (rewrite_link |> hlpred_only_sel)
      ; fold_link |> hlpred_only_sel
      ; instantiate_link
      ]
  in

  let srcs, fixed_srcs =
    begin
      match srcsel with
      | [] -> ([ dnd.source ], None)
      | srcs -> ([ mk_ipath (Handle.toint g_id) ], Some srcs)
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
      | dsts -> ([ mk_ipath (Handle.toint g_id) ], Some dsts)
    end
  in

  let open Monad.List in
  srcs >>= fun src ->
  dsts >>= fun dst ->
  let linkactions = search_linkactions hlp proof ?fixed_srcs ?fixed_dsts (src, dst) in

  linkactions >>= fun (((srcs, dsts) as lnk), actions) ->
  let actions = remove_nothing actions in
  srcs >>= fun src ->
  dsts >>= fun dst ->
  return
    { description = "Hyperlink"
    ; icon = None
    ; highlights = srcs @ dsts
    ; kind = `DnD (src, dst)
    ; action = (g_id, `Hyperlink (lnk, actions))
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
    ; action = (gid_of_ipath proof tgt, `Indt tgt)
    }
  in

  let case_eq tgt =
    { description = "Case"
    ; icon = Some "list"
    ; highlights = sel
    ; kind = `Ctxt
    ; action = (gid_of_ipath proof tgt, `Case tgt)
    }
  in

  let pbp tgt =
    { description = "Point"
    ; icon = Some "hand-pointer"
    ; highlights = sel
    ; kind = `Ctxt
    ; action = (gid_of_ipath proof tgt, `Pbp tgt)
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
            ; action = (gid_of_ipath proof tgt, `Simpl tgt)
            }
          ; { description = "Unfold"
            ; icon = Some "magnifying-glass"
            ; highlights = sel
            ; kind = `Ctxt
            ; action = (gid_of_ipath proof tgt, `Red tgt)
            }
          ; induction tgt
          ; case_eq tgt
          ; pbp tgt
          ]
    end
  | _ -> []

let ctxt_actions (sel : selection) (proof : Proof.proof) : aoutput list =
  let selpred = selpred_add [ single_subterm_sel ] in
  selpred proof sel

let actions (proof : Proof.proof) (p : asource) : aoutput list =
  match p.kind with
  | `Click path -> begin
      let Proof.{ g_id = hd; g_pregoal = goal }, item, (_, _) = of_ipath proof path in
      match item with
      | `C _ -> begin
          let iv = ivariants (proof, hd) in
          let bv = List.length iv <= 1 in
          List.mapi
            (fun i x ->
              let hg =
                mk_ipath (Handle.toint hd)
                  ~sub:(if bv then [] else rebuild_pathd (List.length iv) i)
              in
              { description = x
              ; icon = None
              ; highlights = [ hg ]
              ; kind = `Click hg
              ; action = (hd, `Intro i)
              })
            iv
        end
      | `H (rp, _) ->
          let ev = evariants (proof, hd) rp in
          let bv = List.length ev <= 1 in
          List.mapi
            (fun i x ->
              let hg =
                mk_ipath (Handle.toint hd)
                  ~ctxt:{ kind = `Hyp; handle = Handle.toint rp }
                  ~sub:(if bv then [] else rebuild_pathd (List.length ev) i)
              in
              { description = x
              ; icon = None
              ; highlights = [ hg ]
              ; kind = `Click hg
              ; action = (hd, `Elim (rp, i))
              })
            ev
      | `V (x, (ty, None)) when Form.t_equal goal.g_env ty Env.nat ->
          let rp = Vars.getid goal.g_env x |> Option.get in
          let hg =
            mk_ipath (Handle.toint hd) ~ctxt:{ kind = `Var `Head; handle = Handle.toint rp }
          in
          [ { description = "Induction"
            ; icon = None
            ; highlights = [ hg ]
            ; kind = `Click hg
            ; action = (hd, `Ind hd)
            }
          ]
      | `V (x, (_, Some _)) ->
          let rp = Vars.getid goal.g_env x |> Option.get in

          let hg_unfold =
            mk_ipath (Handle.toint hd) ~ctxt:{ kind = `Var `Head; handle = Handle.toint rp }
          in
          let hg_fold =
            mk_ipath (Handle.toint hd) ~ctxt:{ kind = `Var `Body; handle = Handle.toint rp }
          in

          [ { description = "Unfold"
            ; icon = None
            ; highlights = [ hg_unfold ]
            ; kind = `Click hg_unfold
            ; action = (hd, `Unfold x)
            }
          ; { description = "Fold"
            ; icon = None
            ; highlights = [ hg_fold ]
            ; kind = `Click hg_fold
            ; action = (hd, `Fold x)
            }
          ]
      | _ -> []
    end
  | `DnD dnd -> dnd_actions (dnd, p.selection) proof
  | `Ctxt -> ctxt_actions p.selection proof

module Translate = struct
  open Api
  open Fo.Translate
  open Proof
  open Hidmap
  open State

  exception UnsupportedAction of action_type

  let of_ctxt (ctxt : ctxt) : Logic_t.ctxt State.t =
    let* uid =
      match ctxt.kind with
      | `Concl -> return "concl"
      | `Hyp | `Var _ -> find (Handle.ofint ctxt.handle)
    in
    return Logic_t.{ kind = ctxt.kind; handle = uid }

  let of_ipath (p : ipath) : Logic_t.ipath State.t =
    let* ctxt = of_ctxt p.ctxt in
    return Logic_t.{ ctxt; sub = p.sub }

  let of_lenv (lenv : LEnv.lenv) : Fo_t.lenv =
    LEnv.bindings lenv |> List.map (fun (x, ty) -> (x, of_type_ ty))

  let of_itrace (itrace : itrace) : Logic_t.itrace =
    List.map
      begin
        fun (i, w) -> (i, Option.map (fun (le1, le2, e) -> (of_lenv le1, of_lenv le2, of_expr e)) w)
      end
      itrace

  let of_action (proof : Proof.proof) ((hd, a) : action) : Logic_t.action State.t =
    match a with
    | `Intro variant -> return (`AIntro (variant, None))
    | `Elim (subhd, i) ->
        let goal = Proof.byid proof hd in
        let hyp = (Proof.Hyps.byid goal.g_hyps subhd).h_form in
        let exact = Form.f_equal goal.g_env hyp goal.g_goal in
        let* uid = find subhd in
        return (if exact then `AExact uid else `AElim (uid, i))
    | `Lemma name -> return (`ALemma name)
    | `Ind subhd ->
        let* uid = find subhd in
        return (`AInd uid)
    | `Simpl tgt ->
        let* tgt = of_ipath tgt in
        return (`ASimpl tgt)
    | `Red tgt ->
        let* tgt = of_ipath tgt in
        return (`ARed tgt)
    | `Indt tgt ->
        let* tgt = of_ipath tgt in
        return (`AIndt tgt)
    | `Case tgt ->
        let* tgt = of_ipath tgt in
        return (`ACase tgt)
    | `Pbp tgt ->
        let* tgt = of_ipath tgt in
        return (`APbp tgt)
    | `Hyperlink (lnk, actions) -> begin
        match (lnk, actions) with
        | ([ src ], [ dst ]), [ `Subform substs ] ->
            let _, itrace = dlink (src, dst) substs proof in
            let* src = of_ipath src in
            let* dst = of_ipath dst in
            return (`ALink (src, dst, of_itrace itrace))
        | _, [ `Instantiate (wit, tgt) ] ->
            let* tgt = of_ipath tgt in
            return (`AInstantiate (of_expr wit, tgt))
        | _, _ :: _ :: _ -> failwith "Cannot handle multiple link actions yet"
        | _, _ -> raise (UnsupportedAction a)
      end
    | _ -> raise (UnsupportedAction a)

  let export_action hm proof a = run (of_action proof a) hm
end