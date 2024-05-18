(** This module defines some core utilities to manipulate proofs 
    and perform formula linking & interaction. It includes :
    - The notion of proof (module [Proof]) which is the main state of the prover. 
    - Utility functions on paths in a term (module [PathUtils]). 
    - The notion of polarity of a (sub)formula (module [Polarity]). 
*)

open Api
open Lang
open Logic

exception InvalidSubFormPath of int list
exception InvalidSubExprPath of int list
exception SubgoalNotOpened of int

(** This module defines the core datastructure used in the prover : the proof state.
    The proof contains the list of active goals (along with their hypotheses, conclusion, environment)
    and some additional bookkeeping information. *)
module Proof : sig
  exception TacticNotApplicable

  (** Abstract type of a proof state. *)
  type t

  (** Metadata associated to a goal. *)
  type meta = < > Js_of_ocaml.Js.t

  (** Create a fresh proof that contains some goals. *)
  val init : goal list -> t

  (** Test whether the proof has some remaining active goals. *)
  val closed : t -> bool

  (** Return a list of all active goals in the proof. *)
  val opened : t -> int list

  (** Retrieve an active goal by its handle. *)
  val byid : t -> int -> pregoal

  (** Get the lemma database. *)
  val get_db : t -> Lemmas.t

  (** Set the lemma database. *)
  val set_db : t -> Lemmas.t -> t

  (** Attach metadata to a goal. *)
  val set_meta : t -> int -> meta option -> unit

  (** Get the metadata attached to a goal. *)
  val get_meta : t -> int -> meta option

  (** A set of (basic) functions that modify a proof. *)

  (** In a proof, replace a goal by a list of pregoals. 
      Returns the handles of the goals freshly created and the new proof state.
      BEWARE: after calling [xprogress], any [Path.t] into the replaced goal will become invalid 
      (i.e. the [root] field of the [Path.t] will point to a closed goal). *)
  (*val xprogress : t -> int -> pregoal list -> int list * t

    (** Add a local definition (in a given goal). *)
    val add_local_def : t -> goal_id:int -> Name.t * Term.t * Term.t -> t*)

  (** Move a hypothesis BEFORE another hypothesis. *)
  val move : t -> goal_id:int -> hyp_name:Name.t -> dest_name:Name.t option -> t

  (** Get all the introduction variants (in a given goal). *)
  val ivariants : t -> goal_id:int -> string list

  (** Get all the elimination variants of a given hypothesis (in a given goal). *)
  val evariants : t -> goal_id:int -> hyp_name:Name.t -> string list
end

(** Utilities for the module [Logic.Path]. *)
module PathUtils : sig
  (** Make a path to the (root of the) conclusion of a goal. *)
  val to_concl : goal -> Path.t

  (** Destruct a path, i.e. get all the information relevant to a path. *)
  val destr : Path.t -> Proof.t -> goal * item * Context.t * Term.t

  (** Return the goal that contains the path. *)
  val goal : Path.t -> Proof.t -> goal

  (** Return the identifer of the goal that contains the path. *)
  val gid : Path.t -> Proof.t -> int

  (** Return the item that a path point to. *)
  val item : Path.t -> Proof.t -> item

  (** Return the subterm pointed at by the path. *)
  val term : Path.t -> Proof.t -> Term.t

  (** Given that the path points to a subterm [t], return the context that is valid at [t] 
      (i.e. contains local variables bound by quantifiers above [t]). *)
  val ctx : Path.t -> Proof.t -> Context.t
end

(** A subformula can either have a positive polarity [Pos], a negative polarity
    [Neg], or a superposition [Sup] of both.
    The interpretation is that :
    - [Pos] indicates facts that we need to prove (e.g. the conclusion).
    - [Neg] indicates facts that we know (e.g. a hypothesis).
    - [Sup] indicates facts that are both.

    For example in the hypothesis [(A ⇒ B) ∧ (C ⇔ D)], A is positive, B is
    negative, and C and D can be either, depending on the way the user chooses
    to rewrite the equivalence. This coincides with the standard linear logic
    reading of equivalence as the additive conjunction of both directions of an
    implication. 
    
    A subexpression (i.e. a subterm of type other than Prop) has the same polarity as
    the subformula that contains it. *)
module Polarity : sig
  (** A polarity : positive, negative or superposed (i.e. both positive and negative). *)
  type t = Pos | Neg | Sup [@@deriving show]

  (** [opp p] returns the opposite polarity of [p].
      [Sup] is mapped to itself. *)
  val opp : t -> t

  (** [of_subterm (p, t) sub] returns the subterm of [t] at path [sub] together
      with its polarity and context, given that [t]'s polarity is [p].
      Raises [InvalidSubtermPath] if [sub] does not point to a valid subterm in [t]. *)
  val of_subterm : t * Term.t -> int list -> t * Context.t * Term.t

  (** [neg_count t sub] counts the number of negations in [t] along path [sub] *)
  val neg_count : Term.t -> int list -> int

  (** [of_item it] returns the polarity of the item [it]. *)
  val of_item : item -> t

  (** [of_ipath proof path] returns the polarity of the subterm at path [path] in [proof]. 
      Raises an anomaly if [path] points to variable (head or body). *)
  val of_ipath : Proof.t -> Path.t -> t
end
