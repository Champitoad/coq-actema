open Lang

exception InvalidGoalName of Name.t
exception InvalidHyphName of Name.t
exception InvalidLemmaName of Name.t

(***************************************************************************************)
(** Items *)

(** A single hypothesis. *)
type hyp = { h_src : Name.t option; h_gen : int; h_form : Term.t }
[@@deriving show]

(** A module to handle collections of hypotheses. *)
module Hyps : sig
  type t

  val empty : t
  val byid : t -> Name.t -> hyp
  val add : t -> Name.t -> hyp -> t
  val remove : t -> Name.t -> t
  val move : t -> Name.t -> Name.t option -> t
  val bump : t -> t
  val ids : t -> Name.t list
  val map : (hyp -> hyp) -> t -> t
  val iter : (hyp -> unit) -> t -> unit
  val to_list : t -> (Name.t * hyp) list
  val of_list : (Name.t * hyp) list -> t
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
  val byid : t -> Name.t -> lemma
  val add : t -> Name.t -> lemma -> t
  val remove : t -> Name.t -> t
  val ids : t -> Name.t list
  val map : (lemma -> lemma) -> t -> t
  val iter : (lemma -> unit) -> t -> unit
  val filter : (lemma -> bool) -> t -> t
  val to_list : t -> (Name.t * lemma) list
  val of_list : (Name.t * lemma) list -> t
end

(** A single pregoal. *)
type pregoal = { g_env : Env.t; g_hyps : hyp list; g_concl : Term.t }

(** A goal is a pregoal together with a handle. *)
type goal = { g_id : int; g_pregoal : pregoal }

(** An item in a goal. *)
type item =
  | Concl of Term.t  (** Conclusion. *)
  | Hyp of Name.t * hyp  (** Hypothesis. *)
  | Var of Name.t * Term.t * Term.t option  (** Variable. *)
[@@deriving show]

(***************************************************************************************)
(** Paths *)

(** This module defines paths to items.
      A path can point to :
      - A subterm of the conclusion.
      - A subterm of a hypothesis.
      - A variable definition : either to the head (variable name) or a subterm of the definition's body.
      A path points to an item in a specific goal. *)
module Path : sig
  (** What kind of object does a path point to ? *)
  type kind = Hyp | Concl | Var of [ `Head | `Body ] [@@deriving show]

  (** What object does a path point to ?
        Depending on the [kind], the [handle] is :
        - For [Concl], it is always [0].
        - For [Hyp], it is the index of the corresponding hypothesis in the goal.
        - For [Var], it is the index of the corresponding variable binding in the goal's environment. *)
  type ctxt = { kind : kind; handle : int } [@@deriving show]

  (** A path to a subterm of an item.
        As an example, consider the goal :
          [x := 4, y := 3 * x + 2, x + 3 * y = 0 |- x = 0]
        Assuming this is the goal with index 0, possible paths include :
        - [{ root = 0 ; ctxt = { kind = `Concl ; handle = 0 } ; sub = [0] }]
          which points to the variable [x] in the conclusion.
        - [{ root = 0 ; ctxt = { kind = `Var `Body ; handle = 1 } ; sub = [0] }]
          which points to the expression [3 * x] in the definition of [y].
        - [{ root = 0 ; ctxt = { kind = `Var `Head ; handle = 0 } ; sub = [] }]
          which points to the variable name [x] in the definition of [x].
    *)
  type t =
    { root : int  (** The index of the goal we point to. *)
    ; ctxt : ctxt  (** The object we point to. *)
    ; sub : int list  (** The position in the term we point to. *)
    }
  [@@deriving show]

  (** The [string] argument contains the path (encoded as text). *)
  exception InvalidPath of string

  (** [make ?ctxt ?sub root] creates a new path in the subgoal with index [root]. *)
  val make : ?ctxt:ctxt -> ?sub:int list -> int -> t

  (** Decode a path encoded as a string. *)
  val of_string : string -> t

  (** Encode a path to a string. *)
  val to_string : t -> string

  (** [subpath p1 p2] checks whether [p1] is a subpath of [p2]. *)
  val subpath : t -> t -> bool

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
