(** This module defines deep interaction between formulas,
    which is the next step after subformula linking.
    See the comment at the start of [link.mli] for an overview.
    
    Deep interaction could eventually migrate to the plugin side : 
    instead of returning a list of [choice] to the plugin, we would return 
    a link and a pair of substitutions. Not sure it is worth the effort though. *)

open Api_new
open Lang
open Logic
open Link

(** A [choice] corresponds to a single choice of rule. 
    
    The [int] is used in case several rules are applicable to a link.
    For instance in [A ∧ {B} |- {B} ∧ A], we could apply : 
    - (L∧₂) corresponding to 0
    - (R∧₁) corresponding to 1
    In general 0 is for the left-hand-side rule and 1 is for the right-hand-side rule.
    
    The optional argument is used for binders, to indicate whether the bound variable is instantiated,
    and if yes with what expression (which depends on the variables bound above in each linked formula). *)
type choice = int * (Context.t * Context.t * Term.t) option

(** An [itrace] is the list of all choices we made in a deep interaction. *)
type itrace = choice list

(** Convert a [choice] to a [string]. *)
val show_choice : Env.t -> choice -> string

(** Convert an [itrace] to a [string]. *)
val show_itrace : Env.t -> itrace -> string

(** [dlink] stands for deep linking, and implements the deep interaction phase
    à la Chaudhuri for intuitionistic logic (i.e. ).
    The list of rules and explanations are available in :
        "A Drag-and-Drop Proof Tactic"
        http://www.lix.polytechnique.fr/Labo/Pablo.DONATO/papers/cpp-article.pdf *)
val dlink : link -> Form.Subst.subst * Form.Subst.subst -> Proof.t -> itrace
