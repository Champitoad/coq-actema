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
    1. The user links the two occurences of the formula {B}.
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

       Choosing an order for the rules is important as the rewrite system 
       is non-confluent (see the paper "A drag and drop proof tactic"). *)

open Api
open Utils
open Lang
open Logic
open CoreLogic

(** A link is simply a pair of a source path and destination path.
    You are NOT supposed to link two subterms of a same item. *)
type link = Path.t * Path.t [@@deriving show]

(** A hyperlink relaxes the constraint that there is only one source and one destination.
    You are NOT supposed to link two subterms of a same item. *)
type hyperlink = Path.t list * Path.t list [@@deriving show]

(** Graphs with integer vertices. *)

module IntGraph : Graph.Sig.P

(** An item in a substitution's mapping. *)
type sitem =
  | (* This variable is rigid : it cannot be substituted.
       In other terms it NOT a unification variable. *)
    SRigid
  | (* This variable is flexible : it can be substituted.
       In other it is a unification variable that has not been instantiated. *)
    SFlex
  | (* This variable is a unification variable that has been substituted.
       The term can still contain more [SFlex] of [Sbound] variables. *)
    SBound of Term.t
[@@deriving show]

(** A subtitution is the result of unifying the two sides of a link [(t1, t2)].
    For practical reasons I chose to work with de Bruijn indices directly instead of 
    using explicit unification variables.

    When unifying [t1] and [t2], the free variables of [t2] are "lifted" above those of [t1],
    i.e. we add [n_free_1] to each free variable of [t2]. 
    This way we can see [t1] and [t2] as living in a "common context" 
    that has [n_free_1] + [n_free_2] variables. *)
type subst =
  { (* The number of free variables of [t1]. *)
    n_free_1 : int
  ; (* The number of free variables of [t2] (before lifting [t2]). *)
    n_free_2 : int
  ; (* The actual substitution. It maps the free variables of the common context
       to terms that depend on these free variables.

       The domain of the mapping should be [0 ... n_free_1 + n_free_2 - 1]. *)
    mapping : sitem IntMap.t
  ; (* A graph on the variables of the common context.
       An edge [i -> j] means that variable [i] depends on variable [j], i.e.
       that [j] is in the free variables of [mapping[i]].

       In a well-formed substitution, this graph is acyclic.
       Moreover a topological sort of the graph should give an interleaving of
       the free variables of [t1] and [t2]. *)
    deps : IntGraph.t
  }
[@@deriving show]

(** An action to perform after linking has been checked. *)
type linkaction =
  | Nothing
  | Both of linkaction * linkaction
  | Subform of subst  (** Subformula linking. This includes deep rewrites. *)
  | Instantiate of Term.t * Path.t
  | Rewrite of Term.t * Term.t * Path.t list
      (** Rewrite expression [e1] into [e2] at several paths. *)
  | Fold of Name.t * Path.t list
  | Unfold of Name.t * Path.t list
[@@deriving show]

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
  type lpred = Proof.t -> link -> linkaction list

  (** A hyperlink predicate. *)
  type hlpred = Proof.t -> hyperlink -> linkaction list

  (** [search_linkactions hlp proof (src, dst)] returns all links between
      subterms of [src] and [dst] in [proof] that can interact according to
      the hyperlink predicate [hlp], together with the lists of possible link
      actions determined by the predicate.
   
      If [fixed_srcs] (resp. [fixed_dsts]) is set, the function returns only
      hyperlinks with sources [fixed_srcs] (resp. destinations [fixed_dsts]),
      and whose destinations (resp. sources) are subterms of [dst] (resp.
      [src]). *)
  val search_linkactions :
       ?fixed_srcs:Path.t list
    -> ?fixed_dsts:Path.t list
    -> hlpred
    -> Proof.t
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

  (** [Pred.if_empty p1 p2] is equivalent to [p1] at links where it is non-empty, 
      and [p2] elsewhere. *)
  val if_empty : hlpred -> hlpred -> hlpred

  (** [Pred.unifiable proof (src, dst)] checks that [src] and [dst] lead to either :
      - two unifiable formulas.
      - two unifiable expressions, that additionnally have the same type. 
      If this check succeeds, returns a `Subform linkaction. *)
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
