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


let mk_ipath ?(ctxt : ctxt = { kind = `Concl; handle = 0 }) ?(sub : int list = []) (root : int) =
  { root; ctxt; sub }

let item_ipath { root; ctxt; _ } = { root; ctxt; sub = [] }
let concl_ipath Proof.{ g_id; _ } = mk_ipath (Handle.toint g_id)

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

let destr_ipath (proof : Proof.proof) (p : ipath) : Proof.goal * item * (uid list * term) =
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
  let g, _, _ = destr_ipath proof p in
  g

let gid_of_ipath (proof : Proof.proof) (p : ipath) : Handle.t = (goal_of_ipath proof p).g_id

let term_of_ipath (proof : Proof.proof) (p : ipath) : term =
  let _, _, (_, t) = destr_ipath proof p in
  t

let env_of_ipath (proof : Proof.proof) (p : ipath) : env =
  let goal, item, (sub, _) = destr_ipath proof p in
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
  let _, item, (sub, _) = destr_ipath proof p in
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
  let _, item_src, (sub_src, _) = destr_ipath proof src in
  let _, item_dst, (sub_dst, _) = destr_ipath proof dst in

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
  let { g_pregoal = goal; _ }, item_src, (sub_src, t_src) = destr_ipath proof src in
  let _, item_dst, (sub_dst, t_dst) = destr_ipath proof dst in

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

  (* I had to refactor [backward_core] out of [backward] to "fix" a very weird bug
     involving pattern matching. It might be related to the following compiler bug :
     https://github.com/ocaml/ocaml/issues/7241 *)
  let backward_core (ctx : fctx) (s : ((LEnv.lenv * subst) * (LEnv.lenv * subst)) ref)
      (switch_pol : bool ref)
      ((((l, lsub) as h), ((r, rsub) as c)) as linkage : (form * int list) * (form * int list)) =
    let ((env1, s1) as es1), ((env2, s2) as es2) = !s in
    begin
      match linkage with
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

  let rec backward (ctx : fctx) (itrace : itrace) (s : (LEnv.lenv * subst) * (LEnv.lenv * subst))
      (((l, _), (r, rsub)) as linkage : (form * int list) * (form * int list)) : form * itrace =
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
          backward_core ctx s switch_pol linkage
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
