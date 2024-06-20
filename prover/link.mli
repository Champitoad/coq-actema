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

(** After having unified the two sides of a link, we gathered some data that 
    we want to keep around. *)
type unif_data =
  { (* The context with domain [fvars_1 @ fvars_2]. *)
    context : Context.t
  ; (* A closed and acyclic substitution with domain [fvars_1 @ fvars_2],
       which unifies the left and right subterm of the link. *)
    subst : Unif.subst
  ; (* The free variables (FVars) bound in the left-hand-side term.
       The variables are ordered from the root to the pointed subterm. *)
    fvars_1 : FVarId.t list
  ; (* The free variables (FVars) bound in the right-hand-side term.
       The variables are ordered from the root to the pointed subterm. *)
    fvars_2 : FVarId.t list
  }
[@@deriving show]

(** An action to perform after linking has been checked. *)
type linkaction =
  | (* Subformula interaction. *)
    Subform of unif_data
  | (* Deep rewrite where the equality is on the left side. *)
    RewriteL of unif_data
  | (* Deep rewrite where the equality is on the right side. *)
    RewriteR of unif_data
[@@deriving show]

(*| Instantiate of hyperlink * Term.t * Path.t
  | Rewrite of hyperlink * Term.t * Term.t * Path.t list
      (** Rewrite expression [e1] into [e2] at several paths. *)
  | Fold of hyperlink * Name.t * Path.t list
  | Unfold of hyperlink * Name.t * Path.t list*)

(*type linkaction =
    (* [DnD (xs, ys, subst, ctx, type)] represents subformula linking, including deep rewrites.
       - [xs] contains the identifers of the bound variables on the left path.

       - [ys] is analogous to [xs] but for the right path.
       - [ctx] is a context with domain [xs @ ys].

       For instance a link [forall x, exists y, {x + y} <link> {2 + 3}] yields :
         Subform ([fvar_x, fvar_y], [], [fvar_x := 2; fvar_y := 3], ctx)
    *)
    | DnD of FVarId.t list * FVarId.t list * Unif.subst * Context.t * dnd_type
  [@@deriving show]*)

(** Lift a link into a hyperlink. *)
val hyperlink_of_link : link -> hyperlink

(** Hyperlink predicates. 
    
    A hyperlink predicate is essentially a function from a hyperlink to an arbitrary type, 
    which has access to the proof state and can fail. We model a hyperlink with result type ['a] 
    as a function [Proof.t -> hyperlink -> 'a option]. 
    
    Hyperlinks form a monad (a combination of the reader and option monads), which allows 
    for a somewhat nice programming interface. *)
module Pred : sig
  (** Monadic interface. *)
  include Utils.Monad.SPlus with type 'a t = Proof.t -> hyperlink -> 'a option

  (** The hyperlink which always fails. This is a synonym of [mzero]. *)
  val fail : 'a t

  (** [unifiable] checks that the hyperlink is of the form [([src], [dst])] 
      where [src] and [dst] lead to unifiable formulas in the first-order skeleton 
      of their respective items. They can also lead to an argument of an equality 
      (still in the first-order skeleton).
      
      If this check succeeds returns the unification data (including the substitution). *)
  val unifiable : unif_data t

  (** [opposite_pol_formulas] checks that the hyperlink is of the form [([src], [dst])]
      where [src] and [dst] lead to formulas of opposite polarities. *)
  val opposite_pol_formulas : unit t

  (** [neg_eq_operand] checks that the hyperlink is of the form [([src], [dst])]
      where either [src] or [dst] leads to the left or right argument of an equality, 
      and that this equality has a negative polarity. If this succeeds it returns the side which
      contains the equality : [`Left] for [src] and [`Right] for [dst]. *)
  val neg_eq_operand : [ `Left | `Right ] t

  (** [wf_subform] checks that the hyperlink is of the form [([src], [dst])]
      where [src] and [dst] lead to unifiable subformulas of opposite polarities, 
      and returns a [Subform] linkaction. *)
  val wf_subform : linkaction t

  (** [deep_rewrite] checks that the hyperlink is of the form [([src], [dst])]
      where [src] and [dst] lead to unifiable expressions, and additionally that either [src] 
      or [dst] leads to the left or right side of an equality that has a negative polarity.
      If it succeeds it returns a [RewriteL] or [RewriteL] linkaction. *)
  val deep_rewrite : linkaction t

  (** [intuitionistic] checks that the hyperlink is of the form [([src], [dst])]
      where [(src, dst)] form an intuitionistic link. *)
  val intuitionistic : unit t

  (*(** [Pred.instantiate proof (srcs, dsts)] checks if [srcs] (resp.
        [dsts]) leads to an expression, and [dsts] (resp. [srcs]) leads either to
        an instantiable quantified subformula, or the set of occurrences of an
        instantiable quantified variable. It it succeeds, it returns the
        corresponding [`Instantiate] link action. *)
    val instantiate : linkaction t

    (** [Pred.rewrite lnk] checks if [lnk] is a rewrite hyperlink. That is, one
        end of the link is the left or right-hand side expression [e] of an
        equality hypothesis, and the other end a non-empty set of arbitrary
        subterms where all occurrences of [e] are to be rewritten.

        If the check succeeds, it returns a [`Rewrite (red, res, tgts)] link
        action, where [red] and [res] are respectively the reduced ([e]) and
        residual expressions, and [tgts] are the targeted subterms.

        This does NOT allow deep rewriting (i.e. the equality must be at the root of a hypothesis). *)
    val rewrite : linkaction t

    (** [Pred.fold lnk] checks if [lnk] is a fold hyperlink. That is, one
        end of the link is the head [x] (resp. body [e]) of a local variable
        definition, and the other end a non-empty set of arbitrary subterms where
        all occurrences of [x] (resp. [e]) are to be rewritten into [e] (resp.
        [x]).

        If the check succeeds, it returns either a [`Fold] or [`Unfold] link action. *)
    val fold : linkaction t*)
end
