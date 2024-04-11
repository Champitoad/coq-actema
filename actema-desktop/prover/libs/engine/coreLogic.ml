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

module Polarity = struct
  type t = Pos | Neg | Sup

  let opp = function Pos -> Neg | Neg -> Pos | Sup -> Sup

  let of_direct_subform ((p, f) : t * form) (i : int) =
    match f with
    | FConn (c, fs) ->
        let subp = match (c, i) with `Imp, 0 | `Not, 0 -> opp p | `Equiv, _ -> Sup | _, _ -> p in
        let subf = try List.at fs i with Invalid_argument _ -> raise (InvalidSubFormPath [ i ]) in
        (subp, subf)
    | FBind (_, _, _, subf) -> (p, subf)
    | _ -> raise (InvalidSubFormPath [ i ])

  let of_direct_subterm ((p, t) : t * term) (i : int) =
    match (t, direct_subterm t i) with
    | `F f, `F _ ->
        let p, f = of_direct_subform (p, f) i in
        (p, `F f)
    | _, t -> (p, t)

  let of_subform (p, f) sub =
    try List.fold_left of_direct_subform (p, f) sub
    with InvalidSubFormPath _ -> raise (InvalidSubFormPath sub)

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

  let of_item = function `H _ -> Neg | `C _ -> Pos | `V _ -> Neg

  let of_ipath (proof : Proof.proof) (p : ipath) : t =
    let _, item, (sub, _) = destr_ipath proof p in
    let pol, form =
      match item with
      | `H (_, { h_form = f; _ }) -> (Neg, f)
      | `C f -> (Pos, f)
      | `V _ -> raise (InvalidSubFormPath sub)
    in
    of_subform (pol, form) sub |> fst
end
