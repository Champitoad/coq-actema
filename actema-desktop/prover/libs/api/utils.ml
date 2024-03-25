open Fo_t
open Logic_t

module Uid : sig
  include Map.OrderedType

  val fresh : unit -> unit -> t
end with type t = int = struct
  type t = int
  
  let compare = Int.compare

  let fresh () : unit -> t =
    let count = ref (-1) in
    fun () -> incr count; !count
end

module Env = struct
  let empty =
    Fo_t.{ env_sort = []; env_prp = []; env_fun = [];
           env_sort_name = []; env_prp_name = []; env_fun_name = [];
           env_var = [] }
  
  let concat e1 e2 =
    Fo_t.{
      env_sort = e1.env_sort @ e2.env_sort;
      env_prp = e1.env_prp @ e2.env_prp;
      env_fun = e1.env_fun @ e2.env_fun;
      env_sort_name = e1.env_sort_name @ e2.env_sort_name;
      env_prp_name = e1.env_prp_name @ e2.env_prp_name;
      env_fun_name = e1.env_fun_name @ e2.env_fun_name;
      env_var = e1.env_var @ e2.env_var; }
end

module LEnv = struct
  let exists lenv x =
    List.exists (fun (y, _) -> x = y) lenv
    
  let enter lenv x ty =
    (x, ty) :: lenv
end

module Vars = struct
  let fresh = Uid.fresh ()

  let get (env : env) name =
    List.assoc_opt name env.env_var

  let push (env : env) ((name, bvar) : name * bvar) =
    let env_var = (name, bvar) :: env.env_var in
    { env with env_var }
  
  let push_lenv (env : env) (lenv : lenv) : env =
    List.fold_left begin fun env (x, ty) ->
        push env (x, (ty, None))
      end env lenv

  let byid env id =
    let open Monads.Option in
    let* body = List.assoc_opt id env.env_var in
    return body
end

module Funs = struct
  let get (env : env) (name : name) =
    List.assoc_opt name env.env_fun
end

exception TypingError

let t_equal (ty1 : type_) (ty2 : type_) =
  match ty1, ty2 with
  | `TVar a, `TVar b ->
      a = b

let rec einfer (env : env) (e : expr) : type_ =
  match e with
  | `EVar x -> begin
      match Vars.get env x with
      | None          -> raise TypingError
      | Some (xty, _) -> xty
    end

  | `EFun (f, args) -> begin
      match Funs.get env f with
      | None -> raise TypingError
      | Some (fargs, fres) ->
          if List.length fargs <> List.length args then
            raise TypingError;
          let args = List.map (einfer env) args in
          if not (List.for_all2 t_equal fargs args) then
            raise TypingError;
          fres
    end

let term_of_expr e : term = `E e
let term_of_form f : term = `F f

let expr_of_term (t : term) =
  match t with
  | `E e -> e
  | _ -> raise (Invalid_argument "Expected an expression")

let form_of_term (t : term) =
  match t with
  | `F f -> f
  | _ -> raise (Invalid_argument "Expected a formula")

exception InvalidPath of ipath
exception InvalidSubFormPath of int list
exception InvalidSubExprPath of int list

let direct_subforms = function
  | `FTrue | `FFalse | `FPred _ -> []
  | `FConn (_, fs) -> fs
  | `FBind (_, _, _, f) -> [f]

let direct_subexprs = function
  | `EVar _ -> []
  | `EFun (_, es) -> es

let direct_subterms : term -> term list = function
  | `F `FPred (_, es) -> List.map term_of_expr es
  | `F f -> List.map term_of_form (direct_subforms f)
  | `E e -> List.map term_of_expr (direct_subexprs e)

let direct_subterm (t : term) (i : int) : term =
  try List.nth (direct_subterms t) i
  with Failure _ ->
    match t with
    | `F `FPred _ | `E _ -> raise (InvalidSubExprPath [i])
    | `F _ -> raise (InvalidSubFormPath [i])

let direct_subform (f : form) (i : int) =
  match direct_subterm (`F f) i with
  | `F f -> f
  | _ -> raise (InvalidSubFormPath [i])

let direct_subexpr (e : expr) (i : int) =
  match direct_subterm (`E e) i with
  | `E e -> e
  | _ -> raise (InvalidSubExprPath [i])

let subterm (t : term) (p : int list) =
  try List.fold_left direct_subterm t p
  with InvalidSubFormPath _ -> raise (InvalidSubFormPath p)
      | InvalidSubExprPath _ -> raise (InvalidSubExprPath p)

let subform (f : form) (p : int list) =
  match subterm (`F f) p with
  | `F f -> f
  | _ -> raise (InvalidSubFormPath p)

let subexpr (e : expr) (p : int list) =
  match subterm (`E e) p with
  | `E e -> e
  | _ -> raise (InvalidSubExprPath p)

type item = [
  | `C of form
  | `H of uid * hyp
  | `V of name * bvar
]

exception InvalidHypId of uid

let byid (hyps : hyp list) (id : uid) =
  try List.find (fun { h_id; _ } -> h_id = id) hyps
  with Not_found ->
    raise (InvalidHypId id)

let of_ipath (goal : goal) (p : ipath)
  : goal * item * (int list * term)
=
  let exn = InvalidPath p in

  let { ctxt; sub; _ } = p in

  let item, t_item =
    match ctxt.kind, ctxt.handle with
    | `Concl, _ ->
        let f = goal.g_concl in
        (`C f, `F f)

    | `Hyp, hd ->
        let { h_form = hf; _ } as hyd =
          byid goal.g_hyps hd in
        (`H (hd, hyd), `F hf)

    | `Var part, hd ->
        let (_, body) as def =
          match Vars.byid goal.g_env hd with
          | Some v -> v | None -> raise exn in
        let expr : Fo_t.expr = match part with
          | `Head -> `EVar hd
          | `Body ->
              match body with
              | Some b -> b | None -> raise exn in
        `V (hd, def), `E expr
  in
  let target = subterm t_item sub in

  (goal, item, (sub, target))

let term_of_ipath (goal : goal) (p : ipath) : term =
  let (_, _, (_, t)) = of_ipath goal p in
  t


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
  | `FConn (c, fs) ->
    let subp =
      match c, i with
      | `Imp, 0 | `Not, 0 -> opp p
      | `Equiv, _ -> Sup
      | _, _ -> p
    in
    let subf =
      try List.nth fs i
      with Invalid_argument _ -> raise (InvalidSubFormPath [i])
    in
    subp, subf
  | `FBind (_, _, _, subf) ->
    p, subf
  | _ -> raise (InvalidSubFormPath [i])

(** [subform_pol (p, f) sub] returns the subformula of [f] at path [sub] together
    with its polarity, given that [f]'s polarity is [p] *)
let subform_pol (p, f) sub =
  try List.fold_left direct_subform_pol (p, f) sub
  with InvalidSubFormPath _ -> raise (InvalidSubFormPath sub)

(** [pol_of_ipath goal p] returns the polarity of the subformula
    at path [p] in [goal] *)
let pol_of_ipath (goal : goal) (p : ipath) : pol =
  let _, item, (sub, _) = of_ipath goal p in
  let pol, form =
    match item with
    | `H (_, { h_form = f; _ }) -> Neg, f
    | `C f -> Pos, f
    | `V _ -> raise (InvalidSubFormPath sub)
  in
  subform_pol (pol, form) sub |> fst


let biniou_unhash_dict = Bi_io.make_unhash [
  "TVar";
  "EVar"; "EFun";
  "And"; "Or"; "Imp"; "Equiv"; "Not";
  "Forall"; "Exist";
  "FTrue"; "FFalse"; "FPred"; "FConn"; "FBind";
  "F"; "E";
  "env_sort"; "env_prp"; "env_fun"; "env_sort_name"; "env_prp_name"; "env_fun_name"; "env_var";
  "h_id"; "h_form";
  "g_env"; "g_hyps"; "g_concl";
  "Hyp"; "Concl"; "Var"; "Head"; "Body";
  "kind"; "pkind"; "handle";
  "uid"; "ctxt"; "sub";
  "AId"; "ADef"; "AIntro"; "AExact"; "AElim"; "AInd"; "ASimpl"; "ARed"; "ACut"; "AGeneralize"; "AMove"; "ADuplicate"; "ALink"; "AInstantiate";
]

let string_of_expr e =
  Bi_io.view ~unhash:biniou_unhash_dict (Logic_b.string_of_expr e)

let string_of_form f =
  Bi_io.view ~unhash:biniou_unhash_dict (Logic_b.string_of_form f)

let string_of_term t =
  Bi_io.view ~unhash:biniou_unhash_dict (Logic_b.string_of_term t)

let string_of_env env =
  Bi_io.view ~unhash:biniou_unhash_dict (Logic_b.string_of_env env)

let string_of_goal goal =
  Bi_io.view ~unhash:biniou_unhash_dict (Logic_b.string_of_goal goal)

let string_of_goals goals =
  Bi_io.view ~unhash:biniou_unhash_dict (Logic_b.string_of_goals goals)

let string_of_itrace itr =
  Bi_io.view ~unhash:biniou_unhash_dict (Logic_b.string_of_itrace itr)

let string_of_action a =
  Bi_io.view ~unhash:biniou_unhash_dict (Logic_b.string_of_action a)

let get_hyp ({ g_hyps; _ } : goal) (id : uid) : hyp =
  List.find (fun { h_id; _ } -> h_id = id) g_hyps