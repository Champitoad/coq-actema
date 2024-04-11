open Fo

exception TacticNotApplicable
exception InvalidSubFormPath of int list
exception InvalidSubExprPath of int list

type targ = Proof.proof * Handle.t
type tactic = targ -> Proof.proof

type item =
  [ `C of form  (** Conslusion. *)
  | `H of Handle.t * Proof.hyp  (** Hypothesis. *)
  | `V of vname * bvar  (** Variable. *) ]

module IPath : sig 
  type pkind = [ `Hyp | `Concl | `Var of [ `Head | `Body ] ]
  type ctxt = { kind : pkind; handle : int }
  type t = { root : int; ctxt : ctxt; sub : int list }
  
  (** The [string] argument contains the path (encoded as text). *)
  exception InvalidPath of string
  
  (** Create a new path. *)
  val make : ?ctxt:ctxt -> ?sub:int list -> int -> t
  (** Destruct a path, i.e. get all the information relevant to a path. *)
  val destr : Proof.proof -> t -> Proof.goal * item * (Utils.uid list * term)

  (** Decode a path encoded as a string. *)
  val of_string : string -> t
  (** Encode a path to a string. *)
  val to_string : t -> string
 
  (** [IPath.subpath p1 p2] checks whether [p1] is a subpath of [p2]. *)
  val subpath : t -> t -> bool

  (** Set the [sub] parts of a path to the empty list. *)
  val erase_sub : t -> t

  (** Make a path to the (root of the) conclusion of a goal. *)
  val to_concl : Proof.goal -> t

  (** Return the goal that contains the path. *)
  val goal : Proof.proof -> t -> Proof.goal
  (** Return the identifer of the goal that contains the path. *)
  val gid : Proof.proof -> t -> Handle.t
  (** Return the subterm pointed at by the path. *)
  val term : Proof.proof -> t -> term
  (** Given that the path points to a subterm [t], return the environment that is valid at [t] 
      (i.e. contains local variables bound by quantifiers above [t]). *)
  val env : Proof.proof -> t -> env
end

val form_of_item : item -> form
val expr_of_item : ?where:[< `Body | `Head > `Body ] -> item -> expr
val term_of_item : ?where:[< `Body | `Head > `Body ] -> item -> term

val add_local_def : string * Fo.type_ * Fo.expr -> tactic
val generalize : Handle.t -> tactic
val move : Handle.t -> Handle.t option -> tactic
val ivariants : targ -> string list
val evariants : targ -> Handle.t -> string list
val direct_subterm : term -> int -> term
val subterm : term -> int list -> term
val modify_direct_subterm : (term -> term) -> term -> int -> term

val modify_subterm :
  ('a -> term -> term) -> (int -> term -> 'a -> 'a) -> 'a -> term -> int list -> term

(** [rewrite_subterm_all env red res t sub] rewrites all occurrences of [red]
      in the subterm of [t] at subpath [sub] into [res], shifting variables in
      [red] and [res] whenever a binder is encountered along the path. *)
val rewrite_subterm_all : env -> term -> term -> term -> int list -> term

(** [rewrite_subterm res t sub] rewrites the subterm of [t] at subpath
            [sub] into [res], shifting variables in [res] whenever a binder is
            encountered along the path. *)
val rewrite_subterm : term -> term -> int list -> term

val subform : form -> int list -> form
val subexpr : term -> int list -> expr

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
    implication. *)
module Polarity : sig
  (** A polarity : positive, negative or superposed (i.e. both positive and negative). *)
  type t = Pos | Neg | Sup

  (** [Polarity.opp p] returns the opposite polarity of [p].
        [Sup] is mapped to itself. *)
  val opp : t -> t

  (** [Polarity.direct_subform_pol (p, f) i] returns the [i]th direct subformula of [f]
          together with its polarity, given that [f]'s polarity is [p] *)
  val of_direct_subform : t * form -> int -> t * form

  (** Assumes both the term and its subterm are formulas, and calls [Polarity.of_direct_subform]. *)
  val of_direct_subterm : t * term -> int -> t * term

  (** [Polarity.subform_pol (p, f) sub] returns the subformula of [f] at path [sub] together
          with its polarity, given that [f]'s polarity is [p] *)
  val of_subform : t * form -> int list -> t * Fo.form

  (** [Polarity.neg_count f sub] counts the number of negations in [f] along path [sub] *)
  val neg_count : form -> int list -> int

  (** [Polarity.of_item it] returns the polarity of the item [it] *)
  val of_item : item -> t

  (** [Polarity.of_ipath proof p] returns the polarity of the subformula
          at path [p] in [proof] *)
  val of_ipath : Proof.proof -> IPath.t -> t
end
