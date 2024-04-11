open Fo

exception TacticNotApplicable
exception InvalidPath of string
exception InvalidSubFormPath of int list
exception InvalidSubExprPath of int list

type targ = Proof.proof * Handle.t
type tactic = targ -> Proof.proof
type path = string
type pkind = [ `Hyp | `Concl | `Var of [ `Head | `Body ] ]
type ctxt = { kind : pkind; handle : int }
type ipath = { root : int; ctxt : ctxt; sub : int list }

type item =
  [ `C of form  (** Conslusion. *)
  | `H of Handle.t * Proof.hyp  (** Hypothesis. *)
  | `V of vname * bvar  (** Variable. *) ]

val form_of_item : item -> form
val expr_of_item : ?where:[< `Body | `Head > `Body ] -> item -> expr
val term_of_item : ?where:[< `Body | `Head > `Body ] -> item -> term
val ipath_of_path : path -> ipath
val path_of_ipath : ipath -> path
val destr_ipath : Proof.proof -> ipath -> Proof.goal * item * (Utils.uid list * term)
val mk_ipath : ?ctxt:ctxt -> ?sub:int list -> int -> ipath
val item_ipath : ipath -> ipath
val concl_ipath : Proof.goal -> ipath
val goal_of_ipath : Proof.proof -> ipath -> Proof.goal
val gid_of_ipath : Proof.proof -> ipath -> Handle.t
val term_of_ipath : Proof.proof -> ipath -> term
val env_of_ipath : Proof.proof -> ipath -> env
val is_sub_path : ipath -> ipath -> bool
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
  val of_ipath : Proof.proof -> ipath -> t
end
