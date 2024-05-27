open Lang

exception InvalidGoalId of int
exception InvalidVarName of Name.t
exception InvalidHyphName of Name.t
exception InvalidLemmaName of Name.t

(***************************************************************************************)
(** First-order. *)

(** Extracting the first-order skeleton of terms. *)
module FirstOrder : sig
  type bkind = Forall | Exist [@@deriving show]
  type conn = True | False | Not | Or | And | Equiv [@@deriving show]

  (** This type represents a term and gives us additional information about
      its first-order structure. *)
  type t =
    | FAtom of Term.t (* A wrapper around an arbitrary term. *)
    | FConn of conn * t list (* A logical connective, EXCEPT implication. *)
    | FImpl of t * t (* Logical implication. *)
    | FBind of bkind * Name.t * Term.t * t (* Logical quantifier. *)
  [@@deriving show]

  (** [of_term ?context env t] destructs the term [t] into an element of the inductive type [t].
      For instance the term [forall x : nat, x = x + 1 \/ P] gets destructed into
      [FBind (Forall, x, nat, FConn (Or, [FAtom (x = x + 1); FAtom P]))]. *)
  val of_term : ?context:Context.t -> Env.t -> Term.t -> t

  (** [to_term fo] is the inverse of [term_to_fo]. It takes an element of the inductive type
      [t] and reconstructs the term that it represents. *)
  val to_term : t -> Term.t
end

(***************************************************************************************)
(** Items *)

(** A single variable. *)
type var = { v_name : Name.t; v_type : Term.t; v_body : Term.t option }
[@@deriving show]

(** A module to handle collections of variables. *)
module Vars : sig
  type t

  val empty : t
  val by_name : t -> Name.t -> var
  val add : t -> var -> t
  val remove : t -> Name.t -> t
  val move : t -> Name.t -> Name.t option -> t
  val names : t -> Name.t list
  val map : (var -> var) -> t -> t
  val iter : (var -> unit) -> t -> unit
  val to_list : t -> var list
  val of_list : var list -> t
end

(** A single hypothesis. *)
type hyp = { h_name : Name.t; h_gen : int; h_form : Term.t } [@@deriving show]

(** A module to handle collections of hypotheses. *)
module Hyps : sig
  type t

  val empty : t
  val by_name : t -> Name.t -> hyp
  val add : t -> hyp -> t
  val remove : t -> Name.t -> t
  val move : t -> Name.t -> Name.t option -> t
  val bump : t -> t
  val names : t -> Name.t list
  val map : (hyp -> hyp) -> t -> t
  val iter : (hyp -> unit) -> t -> unit
  val to_list : t -> hyp list
  val of_list : hyp list -> t
end

(** A single lemma. *)
type lemma =
  { l_full : Name.t
        (** The full name of the lemma. This uniquely identifies the lemma. *)
  ; l_user : Name.t  (** The name to show to the user. *)
  ; l_form : Term.t  (** The statement of the lemma. *)
  }
[@@deriving show]

(** A module to handle a collection of lemmas together with an environment to type the lemmas.
    This environment is kept seperate from the environment of each subgoal.  *)
module Lemmas : sig
  type t

  val empty : t
  val extend_env : Env.t -> t -> t
  val env : t -> Env.t
  val by_name : t -> Name.t -> lemma
  val add : t -> lemma -> t
  val remove : t -> Name.t -> t
  val names : t -> Name.t list
  val map : (lemma -> lemma) -> t -> t
  val iter : (lemma -> unit) -> t -> unit
  val filter : (lemma -> bool) -> t -> t
  val to_list : t -> lemma list
  val of_list : lemma list -> t
end

(** A single pregoal. *)
type pregoal =
  { g_env : Env.t; g_vars : Vars.t; g_hyps : Hyps.t; g_concl : Term.t }

(** A goal is a pregoal together with a handle. *)
type goal = { g_id : int; g_pregoal : pregoal }

(** An item in a goal. *)
type item =
  | Concl of Term.t  (** Conclusion. *)
  | Hyp of Name.t * hyp  (** Hypothesis. *)
  | Var of Name.t * Term.t * Term.t option
      (** Variable. The first term is the variable's type, 
          the second (optional) term is the variable's body. *)
[@@deriving show]

(** [term_of_item item] gets the term contained in the conlusion or hypothesis [item]. 
    @raise Invalid_argument if [item] is a variable. *)
val term_of_item : item -> Term.t

(***************************************************************************************)
(** Paths *)

(** This module defines paths to items.
      A path can point to :
      - A subterm of the conclusion.
      - A subterm of a hypothesis.
      - A variable definition : either to the head (variable name) or a subterm of the definition's body.
      A path points to an item in a specific goal. *)
module Path : sig
  (** What object does a path point to ? *)
  type kind = Hyp of Name.t | Concl | VarHead of Name.t | VarBody of Name.t
  [@@deriving show]

  (** A path to a subterm of an item.
      As an example, consider the goal :
        [x := 4, y := 3 * x + 2, x + 3 * y = 0 |- x = 0]
      Assuming this is the goal with index 0, possible paths include :
      - [{ goal = 0 ; kind = Concl } ; sub = [2] }]
        which points to the variable [x] in the conclusion.
      - [{ goal = 0 ; kind = VarBody "y" ; sub = [1] }]
        which points to the expression [3 * x] in the definition of [y].
      - [{ goal = 0 ; kind = VarHead "x" ; sub = [] }]
        which points to the variable name [x] in the definition of [x].
    *)
  type t =
    { goal : int  (** The index of the goal we point to. *)
    ; kind : kind  (** The object we point to. *)
    ; sub : int list  (** The position in the term we point to. *)
    }
  [@@deriving show]

  (** The [string] argument contains the path (encoded as text). *)
  exception InvalidPath of string

  (** [make ?kind ?sub goal] creates a new path in the subgoal with index [goal].
      By default [kind] is [Concl] and [sub] is [[]].  *)
  val make : ?kind:kind -> ?sub:int list -> int -> t

  (** Decode a path encoded as a string. *)
  val of_string : string -> t

  (** Encode a path to a string. *)
  val to_string : t -> string

  (** [same_item p1 p2] checks whether [p1] and [p2] point to the same item.
      A variable's head and body are considered the same item. *)
  val same_item : t -> t -> bool

  (** [is_prefix p1 p2] checks whether [p1] is a prefix of [p2]. This means that :
      - [p1] and [p2] point to the same item.
      - [p1.sub] is a prefix of [p2.sub]. *)
  val is_prefix : t -> t -> bool

  (** Set the [sub] parts of a path to the empty list. *)
  val erase_sub : t -> t
end

(***************************************************************************************)
(** Actions *)

(* Trace of a subformula linking, from which the list of rewrite rules to apply
   can be reconstructed *)
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

(* An action identifier is a pair of an arbitrary string identifier and an abstract goal. *)
type aident = string * hyp list * Term.t [@@deriving show]
