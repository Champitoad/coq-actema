(** This module implements subformula *linking* as defined in :
      "A Drag-and-Drop Proof Tactic"
      http://www.lix.polytechnique.fr/Labo/Pablo.DONATO/papers/cpp-article.pdf

    From a high-level viewpoint :
    1. The user chooses source path(s) and destination path(s) to items in a goal.
    2. We perform subformula linking : check that the link is valid, i.e. can produce
       at least one valid interaction. This is what happens in this file [link.ml], 
       and corresponds roughly to section 9 in the paper.
    3. We perform deep interaction, i.e. we choose an order of application of
       the deep inference rules. This happens in file [interact.ml],
       and corresponds roughly to section 10 in the paper.

    Consider the following example. The user performs the following link 
    (where the linked items are denoted by curly braces) :
      [C ⇒ (A ∧ {B}) * D ∧ {B}]
    The process unfolds as follows :
    1. The user links the two occurences of the formula {B}.
    2. Subformula *linking* checks (among other things) that these subformulas are unifiable
       and of opposite polarities. 
       In this case it is trivial, but in general there can be quantifiers above 
       each linked subformula, making this more tricky. 
    3. We now know that the linked formulas can interact, 
       but they might have more than one possible interaction. 
       Choosing an order for the rules is important as the rewrite system 
       is non-confluent (see the paper for more details). *)

open Api
open Lang
open Logic
open ProverLogic

(** A link is simply a pair of a source path and destination path.
    You are NOT supposed to link two subterms of a same item. *)
type link = Path.t * Path.t [@@deriving show]

(** A hyperlink relaxes the constraint that there is only one source and one destination.
    You are NOT supposed to link two subterms of a same item. *)
type hyperlink = Path.t list * Path.t list [@@deriving show]

(** An action to perform after linking has been checked. *)
type linkaction =
  | Nothing
  | Both of linkaction * linkaction
  (* [Subform (xs, ys, subst, ctx)] represents subformula linking, including deep rewrites.
     - [xs] contains the identifers of the bound variables on the left path.
       The variables are ordered from the root to the pointed subterm.
     - [ys] is analogous to [xs] but for the right path.
     - [subst] is a closed and acyclic substitution with domain [xs @ ys],
       which unifies the left and right subterm of the link.
     - [ctx] is a context with domain [xs @ ys].

     For instance a link [forall x, exists y, {x + y} <link> {2 + 3}] yields :
       Subform ([fvar_x, fvar_y], [], [fvar_x := 2; fvar_y := 3], ctx)
  *)
  | Subform of FVarId.t list * FVarId.t list * Unif.subst * Context.t
(*| Instantiate of Term.t * Path.t
  | Rewrite of Term.t * Term.t * Path.t list
      (** Rewrite expression [e1] into [e2] at several paths. *)
  | Fold of Name.t * Path.t list
  | Unfold of Name.t * Path.t list*)
[@@deriving show]

(** Lift a link into a hyperlink. *)
val hyperlink_of_link : link -> hyperlink

(** Remove all the [Nothing] appearing in a linkaction. *)
val remove_nothing : linkaction -> linkaction option

(** A (hyper)link predicate ([Pred.lpred] and [Pred.hlpred]) captures functions which
    map a (hyper)link in a proof to a list of possible link actions.

    This module defines combinators for working with link predicates 
    as well as some standard predicates. 

    One can emulate a traditional boolean predicate by returning the singleton
    [Nothing] to indicate membership, or the empty list to indicate absence thereof. *)
module Pred : sig
  (** A link predicate. *)
  type lpred = Proof.t -> link -> linkaction list

  (** A hyperlink predicate. *)
  type hlpred = Proof.t -> hyperlink -> linkaction list

  (** Lift a link predicate to a hyperlink predicate. *)
  val lift : lpred -> hlpred

  (** [Pred.mult preds] returns a hyperlink predicate that denotes the cartesian
      product of the actions denoted by the hyperlink predicates in [preds]. 
      
      This evaluates the predicates left to right, 
      and stops as soon as a predicate returns an empty list of linkactions. 
      If e.g. the first predicate returns an empty list,
      the next predicates are not evaluated. *)
  val mult : hlpred list -> hlpred

  (** [Pred.add preds] returns a hyperlink predicate that denotes the disjoint
      union of the actions denoted by the hyperlink predicates in [preds]. *)
  val add : hlpred list -> hlpred

  (** [Pred.if_empty p1 p2] is equivalent to [p1] at links where it is non-empty, 
      and [p2] elsewhere. *)
  val if_empty : hlpred -> hlpred -> hlpred

  (** [Pred.unifiable proof (src, dst)] checks that [src] and [dst] lead to
      unifiable formulas in the first-order skeleton of their respective items.
      They can also lead to an argument of an equality (still in the first-order skeleton).
      
      If this check succeeds, returns a Subform linkaction containing the substitution. *)
  val unifiable : lpred

  (** [Pred.opposite_pol_formulas proof (src, dst)] checks that [src] and [dst]
      lead to formulas of opposite polarities. *)
  val opposite_pol_formulas : lpred

  (** [Pred.neg_eq_operand proof (src, dst)] checks that either [src] or [dst] 
      leads to the left or right argument of an equality, and that this equality 
      has a negative polarity. *)
  val neg_eq_operand : lpred

  (** [Pred.wf_subform proof (src, dst)] checks if [src] and [dst] lead to
      unifiable subformulas of opposite polarities in the focused goal of
      [proof], and returns the associated substitutions if they do inside a
      [`Subform] link action. *)
  val wf_subform : hlpred

  (** [Pred.deep_rewrite proof (src, dst)] checks if [src] and [dst] lead to
      unifiable expressions of the same type, and additionally that either [src] 
      or [dst] leads to the left or right side of an equality that has a negative polarity. *)
  val deep_rewrite : hlpred

  (** [Pred.intuitionistic lnk] checks if [lnk] is an intuitionistic link,
                   and returns a [`Nothing] link action if so. *)
  val intuitionistic : lpred

  (** [Pred.instantiate proof (srcs, dsts)] checks if [srcs] (resp.
      [dsts]) leads to an expression, and [dsts] (resp. [srcs]) leads either to
      an instantiable quantified subformula, or the set of occurrences of an
      instantiable quantified variable. It it succeeds, it returns the
      corresponding [`Instantiate] link action. *)
  val instantiate : hlpred

  (** [Pred.rewrite lnk] checks if [lnk] is a rewrite hyperlink. That is, one
      end of the link is the left or right-hand side expression [e] of an
      equality hypothesis, and the other end a non-empty set of arbitrary
      subterms where all occurrences of [e] are to be rewritten.
             
      If the check succeeds, it returns a [`Rewrite (red, res, tgts)] link
      action, where [red] and [res] are respectively the reduced ([e]) and
      residual expressions, and [tgts] are the targeted subterms. 
      
      This does NOT allow deep rewriting (i.e. the equality must be at the root of a hypothesis). *)
  val rewrite : hlpred

  (** [Pred.fold lnk] checks if [lnk] is a fold hyperlink. That is, one
      end of the link is the head [x] (resp. body [e]) of a local variable
      definition, and the other end a non-empty set of arbitrary subterms where
      all occurrences of [x] (resp. [e]) are to be rewritten into [e] (resp.
      [x]).
             
      If the check succeeds, it returns either a [`Fold] or [`Unfold] link action. *)
  val fold : hlpred
end
