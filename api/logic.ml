(** This file defines the data format used to exchange information 
    between the plugin and the frontend. *)

(* -------------------------------------------------------------------- *)
(** Identifiers *)

type name = string [@@deriving show, yojson]

(* -------------------------------------------------------------------- *)
(** Types *)

type type_ = TVar of name [@@deriving show]
type arity = type_ list [@@deriving show]
type sig_ = arity * type_ [@@deriving show]

(* -------------------------------------------------------------------- *)
(** Expressions *)

type expr = EVar of name | EFun of (name * expr list) [@@deriving show]

(* -------------------------------------------------------------------- *)
(** Formulas *)

type logcon = And | Or | Imp | Equiv | Not [@@deriving show]
type bkind = Forall | Exist [@@deriving show]

type form =
  | FTrue
  | FFalse
  | FPred of (name * expr list)
  | FConn of (logcon * form list)
  | FBind of (bkind * name * type_ * form)
[@@deriving show]

(* -------------------------------------------------------------------- *)
(** Terms = Formulas + Expressions *)

type term = F of form | E of expr [@@deriving show]

(* -------------------------------------------------------------------- *)
(** Environments *)

(* Body of a variable declaration, holding its type and eventually an expression
   in the case of a local definition *)
type bvar = type_ * expr option [@@deriving show]
type varenv = (name * bvar) list [@@deriving show]

type env =
  { env_sort : name list (* Sorts, i.e. atomic types *)
  ; env_prp : (name * arity) list (* Predicate symbols *)
  ; env_fun : (name * sig_) list (* Function symbols *)
  ; env_sort_name : (name * name) list
  ; env_prp_name : (name * name) list
  ; env_fun_name : (name * name) list
  ; env_var : varenv (* Variable declarations *)
  }
[@@deriving show]

(* Local environment, only maps abstract variables to their type *)

(** Goals *)
type lenv = (name * type_) list [@@deriving show]
(* -------------------------------------------------------------------- *)

(* Unique identifier (for a hypothesis or variable for instance). *)
type uid = string [@@deriving show]

(* Hypothesis *)
type hyp = { h_id : uid; h_form : form } [@@deriving show]

(* Goal *)
type goal = { g_env : env; g_hyps : hyp list; g_concl : form } [@@deriving show]
type goals = goal list [@@deriving show]
type lgoal = hyp list * form [@@deriving show]

(* Abstract goal, without the signature *)
type agoal = { a_vars : varenv; a_hyps : hyp list; a_concl : form } [@@deriving show]

(* A lemma has a "user name" : the name we display to the user,
   and a "full name" : a potentially not very readable encoding
   of its name (but still useful for debug purposes).

   For instance the underlying Coq term might be a constant or an inductive constructor,
   and this results in a different full name.

   The prover can think of the full name as an abstract identifier for the lemma. *)
type lemma = { l_user : name; l_full : name; l_stmt : form } [@@deriving show]

(* A lemma database. *)
type lemmadb = env * lemma list [@@deriving show]

(* -------------------------------------------------------------------- *)
(** Actions *)

(* A path refers to a subterm in the current subgoal, through a [handle]
   identifying an item of kind [kind], and a list of integers [sub] designating
   the specific subterm of the item *)
type vkind = Head | Body [@@deriving show]
type pkind = Hyp | Concl | Var of vkind [@@deriving show]
type ctxt = { kind : pkind; handle : uid } [@@deriving show]
type ipath = { ctxt : ctxt; sub : int list } [@@deriving show]

(* Trace of a subformula linking, from which the list of rewrite rules to apply
   can be reconstructed *)
type choice = int * (lenv * lenv * expr) option [@@deriving show]
type itrace = choice list [@@deriving show]

type action =
  | AId (* The empty action which does nothing *)
  | ADef of (name * type_ * expr) (* Introduction of a local definition *)
  | ALemma of name (* Add a lemma to the hypotheses. *)
  | AIntro of (int * (expr * type_) option) (* Click on a conclusion *)
  | AExact of uid (* Proof by assumption *)
  | AElim of (uid * int) (* Click on a hypothesis *)
  | AInd of uid (* Click on a variable of inductive type *)
  | ASimpl of ipath (* Simplify contextual action *)
  | ARed of ipath (* Unfold contextual action *)
  | AIndt of ipath (* Induction contextual action *)
  | APbp of ipath (* Proof-by-Pointing contextual action *)
  | ACase of ipath (* Case contextual action *)
  | ACut of form (* Click on +hyp button *)
  | AGeneralize of uid (* Generalization of a hypothesis *)
  | AMove of (uid * uid option) (* Reordering of a hypothesis *)
  | ADuplicate of uid (* Duplication of a hypothesis *)
  | ALink of (ipath * ipath * itrace) (* DnD action for subformula linking *)
  | AInstantiate of (expr * ipath) (* DnD action for instantiating a quantifier *)
[@@deriving show]

(* An action identifier is a pair of an abstract goal and an arbitrary string identifier *)
type aident = string * lgoal [@@deriving show]
