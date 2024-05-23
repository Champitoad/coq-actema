open Lang
open Batteries

exception InvalidGoalId of int
exception InvalidHyphName of Name.t
exception InvalidLemmaName of Name.t

(***************************************************************************************)
(** First-order terms. *)

module FirstOrder = struct
  type bkind = Forall | Exist [@@deriving show]
  type conn = True | False | Not | Or | And | Equiv [@@deriving show]

  type t =
    | FAtom of Term.t
    | FConn of conn * t list
    | FImpl of t * t
    | FBind of bkind * Name.t * Term.t * t
  [@@deriving show]

  let rec to_term fo : Term.t =
    let open Term in
    match fo with
    | FAtom t -> t
    | FConn (True, []) -> mkCst Name.true_
    | FConn (False, []) -> mkCst Name.false_
    | FConn (Not, [ t ]) -> mkApp (mkCst Name.not) (to_term t)
    | FConn (And, [ t1; t2 ]) ->
        mkApps (mkCst Name.and_) [ to_term t1; to_term t2 ]
    | FConn (Or, [ t1; t2 ]) ->
        mkApps (mkCst Name.or_) [ to_term t1; to_term t2 ]
    | FImpl (t1, t2) -> mkArrow (to_term t1) (to_term t2)
    | FConn (Equiv, [ t1; t2 ]) ->
        mkApps (mkCst Name.equiv) [ to_term t1; to_term t2 ]
    | FBind (Forall, x, ty, body) -> mkProd x ty (to_term body)
    | FBind (Exist, x, ty, body) ->
        mkApps (mkCst Name.ex) [ ty; mkLambda x ty (to_term body) ]
    | FConn _ -> assert false

  (* We need the context and environment be able to compute the type of the term. *)
  let rec of_term ?(context = Context.empty) env (t : Term.t) : t =
    match t with
    | Cst true_ when Name.equal true_ Name.true_ -> FConn (True, [])
    | Cst false_ when Name.equal false_ Name.false_ -> FConn (False, [])
    | App (Cst not, [ arg ]) when Name.equal not Name.not ->
        FConn (Not, [ of_term ~context env arg ])
    | App (Cst and_, [ arg1; arg2 ]) when Name.equal and_ Name.and_ ->
        FConn (And, [ of_term ~context env arg1; of_term ~context env arg2 ])
    | App (Cst or_, [ arg1; arg2 ]) when Name.equal or_ Name.or_ ->
        FConn (Or, [ of_term ~context env arg1; of_term ~context env arg2 ])
    | Arrow (t1, t2) when Typing.typeof ~context env t = Term.mkProp ->
        FImpl (of_term ~context env t1, of_term ~context env t2)
    | Prod (x, ty, body) when Typing.typeof ~context env t = Term.mkProp ->
        FBind
          (Forall, x, ty, of_term ~context:(Context.push x ty context) env body)
    | App (Cst ex, [ ty; Lambda (x, _, body) ]) when Name.equal ex Name.ex ->
        FBind
          (Exist, x, ty, of_term ~context:(Context.push x ty context) env body)
    | _ -> FAtom t
end

(***************************************************************************************)
(** Items *)

(** A single hypothesis. *)
type hyp = { h_name : Name.t; h_gen : int; h_form : Term.t } [@@deriving show]

(** A module to handle collections of hypotheses. *)
module Hyps = struct
  (** A list of hypotheses, each with a handle. *)
  type t = (Name.t * hyp) list

  let empty : t = []

  let byid (hyps : t) (id : Name.t) =
    Option.get_exn (List.Exceptionless.assoc id hyps) (InvalidHyphName id)

  let add (hyps : t) (id : Name.t) (h : hyp) : t =
    assert (Option.is_none (List.Exceptionless.assoc id hyps));
    (id, h) :: hyps

  let remove (hyps : t) (id : Name.t) : t =
    List.filter (fun (x, _) -> not (Name.equal x id)) hyps

  let move (hyps : t) (from : Name.t) (before : Name.t option) =
    let tg = byid hyps from in
    let hyps = remove hyps from in

    match before with
    | None -> (from, tg) :: hyps
    | Some before ->
        let pos, _ =
          Option.get_exn
            (List.Exceptionless.findi
               (fun _ (x, _) -> Name.equal x before)
               hyps)
            (InvalidHyphName before)
        in
        let post, pre = List.split_at (1 + pos) hyps in
        post @ ((from, tg) :: pre)

  let bump (hyps : t) : t =
    List.map (fun (id, h) -> (id, { h with h_gen = h.h_gen + 1 })) hyps

  let ids (hyps : t) = List.map fst hyps
  let map f (hyps : t) = List.map (fun (id, h) -> (id, f h)) hyps
  let iter f (hyps : t) = List.iter (fun (_handle, hyp) -> f hyp) hyps

  let diff (hs1 : t) (hs2 : t) =
    hs1
    |> List.filter (fun (id, _) ->
           not (List.exists (fun (id', _) -> Name.equal id id') hs2))

  let to_list (hyps : t) = List.map snd hyps
  let of_list hyps : t = List.map (fun h -> (h.h_name, h)) hyps
end

(** A single lemma. *)
type lemma = { l_full : Name.t; l_user : Name.t; l_form : Term.t }
[@@deriving show]

(** A module to handle a collection of lemmas together with an environment to type the lemmas.
    This environment is kept seperate from the environment of each subgoal.  *)
module Lemmas = struct
  (** Abstract type of a collection of lemmas. It consists in a map from the lemma handle 
      to the lemma statement and (user-facing) name, and an environment to type the lemmas. *)
  type t = { db_env : Env.t; db_map : lemma Name.Map.t }

  let empty = { db_env = Env.empty; db_map = Name.Map.empty }

  let extend_env env lemmas =
    { lemmas with db_env = Env.union lemmas.db_env env }

  let env lemmas = lemmas.db_env

  let byid lemmas id =
    Option.get_exn (Name.Map.find_opt id lemmas.db_map) (InvalidLemmaName id)

  let add lemmas id l = { lemmas with db_map = Name.Map.add id l lemmas.db_map }

  let remove lemmas id =
    { lemmas with db_map = Name.Map.remove id lemmas.db_map }

  let ids lemmas = Name.Map.bindings lemmas.db_map |> List.map fst
  let map f lemmas = { lemmas with db_map = Name.Map.map f lemmas.db_map }
  let iter f lemmas = Name.Map.iter (fun _ -> f) lemmas.db_map

  let filter pred lemmas =
    { lemmas with db_map = Name.Map.filter (fun _ -> pred) lemmas.db_map }

  let to_list lemmas = Name.Map.bindings lemmas.db_map

  let of_list ls =
    { db_env = Env.empty; db_map = Name.Map.of_seq @@ List.to_seq ls }
end

(** A single pregoal. *)
type pregoal = { g_env : Env.t; g_hyps : Hyps.t; g_concl : Term.t }

(** A goal is a pregoal together with a handle. *)
type goal = { g_id : int; g_pregoal : pregoal }

(** An item in a goal. *)
type item =
  | Concl of Term.t  (** Conclusion. *)
  | Hyp of Name.t * hyp  (** Hypothesis. *)
  | Var of Name.t * Term.t * Term.t option  (** Variable. *)
[@@deriving show]

let term_of_item (item : item) : Term.t =
  match item with
  | Concl t -> t
  | Hyp (_, { h_form; _ }) -> h_form
  | _ -> failwith "Logic.term_of_item: got a variable."

(***************************************************************************************)
(** Paths *)

module Path = struct
  type kind = Hyp of Name.t | Concl | VarHead of Name.t | VarBody of Name.t
  [@@deriving show]

  type t = { goal : int; kind : kind; sub : int list } [@@deriving show]

  exception InvalidPath of string

  let make ?(kind = Concl) ?(sub : int list = []) (goal : int) =
    { goal; kind; sub }

  let string_of_kind = function
    | Hyp _ -> "H"
    | Concl -> "C"
    | VarHead _ -> "Vh"
    | VarBody _ -> "Vb"

  let name_of_kind = function
    | Hyp name -> name
    | Concl -> Name.make ""
    | VarHead name -> name
    | VarBody name -> name

  let kind_of_string kind_str name_str =
    match kind_str with
    | "H" -> Hyp (Name.make name_str)
    | "C" -> Concl
    | "Vh" -> VarHead (Name.make name_str)
    | "Vb" -> VarBody (Name.make name_str)
    | _ -> failwith "Logic.kind_of_string: invalid path tag"

  let to_string (p : t) =
    let pp_sub =
      Format.pp_print_list
        ~pp_sep:(fun fmt () -> Format.fprintf fmt "/")
        Format.pp_print_int
    in
    Format.asprintf "%d/%s#%s:%a" p.goal (string_of_kind p.kind)
      (Name.show @@ name_of_kind p.kind)
      pp_sub p.sub

  let of_string (str : string) =
    let goal, kind, sub =
      try
        Scanf.sscanf str "%d/%s@#%s@:%s" (fun x1 x2 x3 x4 ->
            (x1, kind_of_string x2 x3, x4))
      with Scanf.Scan_failure _ | Failure _ | End_of_file ->
        raise (Invalid_argument str)
    in

    if goal < 0 then raise (InvalidPath str);

    let sub =
      let sub = if sub = "" then [] else String.split_on_char '/' sub in

      try List.map int_of_string sub with Failure _ -> raise (InvalidPath str)
    in

    if List.exists (fun x -> x < 0) sub then raise (InvalidPath str);

    { goal; kind; sub }

  let rec is_prefix (xs : 'a list) (pr : 'a list) =
    match (xs, pr) with
    | _, [] -> true
    | x :: xs, y :: pr -> x = y && is_prefix xs pr
    | _, _ -> false

  let subpath p sp =
    (*p.goal = sp.goal && p.kind = sp.kind
      && (p.ctxt.kind = sp.ctxt.kind
         || (p.ctxt.kind = Var `Head && sp.ctxt.kind = Var `Body))
      && is_prefix sp.sub p.sub*)
    failwith "subpath: todo"

  let erase_sub path = { path with sub = [] }
end

(***************************************************************************************)
(** Actions *)

type choice = int * (Context.t * Context.t * Term.t) option [@@deriving show]
type itrace = choice list [@@deriving show]

type action =
  | AId (* The empty action which does nothing *)
  | ADuplicate of Name.t (* Duplicate a hypothesis. *)
  | AClear of Name.t (* Clear a hypothesis. *)
  | ADef of (Name.t * Term.t * Term.t) (* Introduction of a local definition *)
  | AIntro of int
    (* Click on a conclusion.
       The [int] indicates which introduction rule to use (0, 1, 2, etc.).
       Usually it is [0], but for instance when the conclusion is a disjunction
       it can be [0] to choose the left side or [1] to choose the right side. *)
  | AExact of Name.t (* Proof by assumption *)
  | AElim of (Name.t * int) (* Click on a hypothesis *)
  | AInd of Name.t (* Simple induction on a variable (of inductive type). *)
  | ASimpl of Path.t (* Simplify contextual action *)
  | ARed of Path.t (* Unfold contextual action *)
  | AIndt of Path.t (* Induction on a variable deep in the goal. *)
  | ACase of Path.t (* Case contextual action *)
  | ACut of Term.t (* Click on +hyp button *)
  | AGeneralize of Name.t
    (* Generalization of a hypothesis. This uses [generalize dependent]. *)
  | ALink of (Path.t * Path.t * itrace) (* DnD action for subformula linking *)
  | AInstantiate of (Term.t * Path.t)
    (* DnD action for instantiating a quantifier *)
[@@deriving show]

type aident = string * hyp list * Term.t [@@deriving show]
