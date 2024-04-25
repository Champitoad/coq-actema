(** This module implements subformula linking as defined in :
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
      [C ⇒ (A ∧ {B}) |- D ∧ {B}]
    The process unfolds as follows :
    1. The user linked the two occurences of the formula {B}.
    2. Subformula linking checks that these subformulas are unifiable. 
       In this case it is trivial, but in general there can be quantifiers above 
       each linked subformula, making this more tricky. 
       We also check that the link verifies other properties (related to polarities for instance).
    3. We now know that the linked formulas can interact, but they might have more than one possible interaction. 
       For instance we could get the interaction :
             C ⇒ A ∧ {B} |- D ∧ {B} 
       (R∧₂) D ∧ (C ⇒ A ∧ {B} |- {B})
       (L⇒₂) D ∧ C ∧ (A ∧ {B} |- {B})
       ...

       Or we could get the interaction :
             C ⇒ A ∧ {B} |- D ∧ {B} 
       (L⇒₂) C ∧ (A ∧ {B} |- D ∧ {B})
       (R∧₂) C ∧ D ∧ (A ∧ {B} |- {B})
       ...

       Choosing an order for the rules is important as the rewrite system is non-confluent.
*)

open CoreLogic
open Fo

(** A link is simply a pair of a source path and destination path. *)
type link = IPath.t * IPath.t

(** A hyperlink relaxes the constraint that there is only one source and one destination. *)
type hyperlink = IPath.t list * IPath.t list

(** An action to perform after linking has been checked. 
    Not all links entail the same linkaction. *)
type linkaction =
  [ `Nothing
  | `Both of linkaction * linkaction
  | `Subform of Form.Subst.subst * Form.Subst.subst  (** Subformula linking. *)
  | `Instantiate of expr * IPath.t
  | `Rewrite of expr * expr * IPath.t list
    (** Rewrite expression [e1] into [e2] at several paths. *)
  | `Fold of vname * IPath.t list
  | `Unfold of vname * IPath.t list ]

(** Lift a link into a hyperlink. *)
val hyperlink_of_link : link -> hyperlink

(** Remove all the [`Nothing] appearing in a linkaction. *)
val remove_nothing : linkaction -> linkaction option

(** A (hyper)link predicate ([Pred.lpred] and [Pred.hlpred]) captures functions which
    map a (hyper)link in a proof to a list of possible link actions.

    This module defines combinators for working with link predicates 
    as well as some standard predicates. 

    One can emulate a traditional boolean predicate by returning the singleton
    [`Nothing] to indicate membership, or the empty list to indicate absence thereof. *)
module Pred : sig
  (** A link predicate. *)
  type lpred = Proof.proof -> link -> linkaction list

  (** A hyperlink predicate. *)
  type hlpred = Proof.proof -> hyperlink -> linkaction list

  (** [search_linkactions hlp proof (src, dst)] returns all links between
      subterms of [src] and [dst] in [proof] that can interact according to
      the hyperlink predicate [hlp], together with the lists of possible link
      actions determined by the predicate.
   
      If [fixed_srcs] (resp. [fixed_dsts]) is set, the function returns only
      hyperlinks with sources [fixed_srcs] (resp. destinations [fixed_dsts]),
      and whose destinations (resp. sources) are subterms of [dst] (resp.
      [src]). *)
  val search_linkactions :
       ?fixed_srcs:IPath.t list
    -> ?fixed_dsts:IPath.t list
    -> hlpred
    -> Proof.proof
    -> link
    -> (hyperlink * linkaction list) list

  (** Lift a link predicate to a hyperlink predicate. *)
  val lift : lpred -> hlpred

  (** [Pred.mult lps] returns a hyperlink predicate that denotes the cartesian
      product of the actions denoted by the hyperlink predicates in [lps]. *)
  val mult : hlpred list -> hlpred

  (** [Pred.add lps] returns a hyperlink predicate that denotes the disjoint
      union of the actions denoted by the hyperlink predicates in [lps]. *)
  val add : hlpred list -> hlpred

  (** [Pred.if_empty p1 p2] is equivalent to [p1] at links where the
      latter is non-empty, and [p2] elsewhere. *)
  val if_empty : hlpred -> hlpred -> hlpred

  (** [Pred.wf_subform proof (src, dst)] checks if [src] and [dst] lead to
      unifiable subformulas of opposite polarities in the focused goal of
      [proof], and returns the associated substitutions if they do inside a
      [`Subform] link action.
             
      If [drewrite] is set to [true], it only checks for deep rewrite links,
      that is links where one side is a negative equality operand, and the other
      side an arbitrary unifiable subexpression of the same type. *)
  val wf_subform : ?drewrite:bool -> lpred

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
