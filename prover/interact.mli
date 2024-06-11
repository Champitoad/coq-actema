(** This module defines deep interaction between formulas,
    which is the next step after linking.
    See the comment at the start of [link.mli] for an overview.
    
    Deep interaction could eventually migrate to the plugin side : 
    instead of returning an [itrace] to the plugin, we would return 
    a link and a substitution. Not sure it is worth the effort though. *)

open Api
open Lang
open Logic
open ProverLogic

(** [dlink] stands for deep linking, and implements the deep interaction phase
    à la Chaudhuri for intuitionistic logic.
    The list of rules and explanations are available in :
      "A Drag-and-Drop Proof Tactic"
      http://www.lix.polytechnique.fr/Labo/Pablo.DONATO/papers/cpp-article.pdf *)
val dlink :
     Path.t * FVarId.t list
  -> Path.t * FVarId.t list
  -> Unif.subst
  -> Proof.t
  -> Logic.itrace
