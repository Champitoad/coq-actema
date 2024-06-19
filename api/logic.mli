open Utils.Pervasive
open Lang

exception InvalidGoalId of int
exception InvalidVarName of Name.t
exception InvalidHyphName of Name.t
exception InvalidLemmaName of Name.t

(***************************************************************************************)
(** First-order. *)

module FirstOrder : sig
  type bkind = Forall | Exist [@@deriving show]
  type conn = True | False | Not | Or | And | Equiv [@@deriving show]

  (** This type represents a term and gives us additional information about
      its first-order structure. *)
  type t = private
    | FAtom of Term.t (* A wrapper around an arbitrary term. *)
    | FConn of
        conn * Term.t list (* A logical connective, EXCEPT implication. *)
    | FImpl of Term.t * Term.t (* Logical implication. *)
    | FBind of bkind * Term.binder * Term.t * Term.t
      (* Logical quantifier. It contains the binder, the type and the body. *)
  [@@deriving show]

  (** [view context env term] destructs the term [term] into an element of the inductive type [t].
      This assumes [term] contains no loose BVar.

      For instance the term [forall x : nat, x = x + 1 \/ P] gets destructed into
      [FBind (Forall, x, nat, x = x + 1 \/ P)]. *)
  val view : Env.t -> Context.t -> Term.t -> t
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
  val names : t -> Name.t list
  val map : (lemma -> lemma) -> t -> t
  val iter : (lemma -> unit) -> t -> unit
  val filter : (lemma -> bool) -> t -> t
  val sort : (lemma -> lemma -> int) -> t -> t
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
    This is O(1).
    @raise Invalid_argument if [item] is a variable. *)
val term_of_item : item -> Term.t

(***************************************************************************************)
(** Paths *)

(** This module defines paths to items.
    A path points to a subterm of an item in a specific goal. *)
module Path : sig
  (** What object does a path point to ? *)
  type kind =
    (* The goal's conclusion. *)
    | Concl
    (* A named hypothesis. *)
    | Hyp of Name.t
    (* A variable's head, i.e. the variable name. *)
    | VarHead of Name.t
    (* A variable's type. *)
    | VarType of Name.t
    (* A variable's body. Note that not all variables have a body. *)
    | VarBody of Name.t
  [@@deriving show]

  (** A path to a subterm of an item.
      As an example, consider the goal :
        [x : nat := 4, y : nat := 3 * x + 2, x + 3 * y = 0 |- x = 0]
      Assuming this is the goal with index 0, possible paths include :
      - [{ goal = 0 ; kind = Concl } ; sub = [2] }]
        which points to the variable [x] in the conclusion.
      - [{ goal = 0 ; kind = VarBody "y" ; sub = [1] }]
        which points to the expression [3 * x] in the variable [y].
      - [{ goal = 0 ; kind = VarHead "x" ; sub = [] }]
        which points to the variable name [x] in the variable [x].
    *)
  type t =
    { goal : int  (** The index of the goal we point to. *)
    ; kind : kind  (** The object we point to. *)
    ; sub : int list
          (** The position in the term we point to. 
              When [kind] is [VarHead _], [sub] should be empty. *)
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
      A variable's head, type and body are considered in the same item. *)
  val same_item : t -> t -> bool

  (** [is_prefix p1 p2] checks whether [p1] is a prefix of [p2]. This means that :
      - [p1.goal] and [p2.goal] are equal.
      - [p1.kind] and [p2.kind] are equal.
      - [p1.sub] is a prefix of [p2.sub]. *)
  val is_prefix : t -> t -> bool

  (** Set the [sub] parts of a path to the empty list. *)
  val erase_sub : t -> t
end

(***************************************************************************************)
(** Actions *)

type action =
  (* The empty action which does nothing *)
  | AId
  (* Duplicate the given hypothesis. *)
  | ADuplicate of Name.t
  (* Clear the given hypothesis. *)
  | AClear of Name.t
  (* Trivially solve the goal with a hypothesis. *)
  | AExact of Name.t
  (* Apply an introduction rule on the conclusion.
     The [int] is used to indicate which introduction rule to use in case of
     ambiguity (e.g. when the conclusion is a disjunction). *)
  | AIntro of int
  (* Apply an elimination rule on a hypothesis.
     The name identifies the hypothesis we are eliminating.
     The [int] indicates which intro rule to use in case of ambiguity
     (for instance when the hypothesis is an equality, it indicates in which direction to rewrite) *)
  | AElim of Name.t * int
  (* Apply Coq's [simpl] tactic to a subterm of an item. *)
  | ASimpl of Path.t
  (* Apply Coq's [destruct] tactic to a term.
     This term must be closed (in the context of the goal).
     For instance in
       x : nat |- forall y : nat, P (x + y)
     we can perform case analysis on [x] in the context, on [x] in the goal,
     but not on [y] or [x + y] in the goal (as these terms contain free variables). *)
  | ACase of Term.t
  (* [ACaseIntro n] assumes the goal starts with [n] universal quantifications or implications,
     performs introduction on them and then case analysis on the last one.
     For instance in
       |- H -> forall x : nat, P x
     performing [ACaseIntro 2] will result in the two goals
       h : H |- P 0
       h : H |- P (S n)
  *)
  | ACaseIntro of int
  (* Same as [ACase] but for induction. *)
  | AInd of Term.t
  (* Same as [ACaseIntro] but for induction. *)
  | AIndIntro of int
  (* Generalize a hypothesis or local variable.
     This changes a goal of the form
        h : H |- C
     into
        |- H -> C
     More precisely this is dependent generalization : any variables / hypothesis that depend on h
     are also generalized. *)
  | AGeneralize of Name.t
  (* Add a lemma to the proof context (i.e. as a hypothesis).
     The [name] contains the full name of the lemma, slightly encoded. *)
  | ALemmaAdd of Name.t
  (* A link (DnD) action. The paths are the two sides of the link. *)
  | ALink of
      (Path.t * FVarId.t list)
      * (Path.t * FVarId.t list)
      * Unif.subst
      * Context.t
(*| ADef of (Name.t * Term.t * Term.t) (* Introduction of a local definition *)
  | ARed of Path.t (* Unfold contextual action *)
  | ACut of Term.t (* Click on +hyp button *)
  | AInstantiate of (Term.t * Path.t)
    (* DnD action for instantiating a quantifier *)*)
[@@deriving show]

(* An action identifier is a pair of an arbitrary string identifier and an abstract goal. *)
type aident = string * hyp list * Term.t [@@deriving show]
