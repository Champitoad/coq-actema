(** This module defines deep interaction between formulas,
    which is the next step after linking.
    See the comment at the start of [link.mli] for an overview.
    
    Deep interaction could eventually migrate to the plugin side : 
    instead of returning an [itrace] to the plugin, we would return 
    a link and a substitution. Not sure it is worth the effort though. *)

open Api
open Lang
open Logic

(** A side in a link. *)
type side = Left | Right [@@deriving show]

(** Maps [Left] to [Right] and vice-versa. *)
val opp_side : side -> side

(** A [choice] corresponds to a single choice of rule.

      The [side] is used in case both a left and right rule are applicable to a link.
      For instance in [A ∧ {B} |- {B} ∧ A], we could apply :
      - (L∧₂) corresponding to Side Left
      - (R∧₁) corresponding to Side Right

      The optional argument in Binder indicates whether the bound variable is instantiated,
      and if yes with what witness (which depends on the variables bound in each linked formula).
      The witness contains BVars from the left *and* right sides. *)
type choice =
  | (* Simply descent in the subformula on the given side. *)
    Side of side
  | (* Traverse a binder on the given side. The optional argument contains the
       instantiation witness. *)
    Binder of side * Term.t option
[@@deriving show]

(** An itrace [fvars_left, fvars_right, choices] contains :
      - The list of choices made during the interaction (see prover/interact.ml).
        The witnesses have free variables in [fvars_left @ fvars_right].
      - The list of FVars bound in the left subterm.
      - The list of FVars bound in the right subterm. *)
type itrace = choice list * FVarId.t list * FVarId.t list [@@deriving show]

(** [dlink] stands for deep linking, and implements the deep interaction phase
    à la Chaudhuri for intuitionistic logic.
    The list of rules and explanations are available in :
      "A Drag-and-Drop Proof Tactic"
      http://www.lix.polytechnique.fr/Labo/Pablo.DONATO/papers/cpp-article.pdf *)
val dlink :
     Path.t * FVarId.t list
  -> Path.t * FVarId.t list
  -> Unif.subst
  -> Logic.pregoal
  -> itrace
