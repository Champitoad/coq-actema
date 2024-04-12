(** This module defines deep interaction between formulas,
    which is the next step after subformula linking.
    See the comment at the start of [link.mli] for an overview. *)

open Link
open Fo

type choice = int * (LEnv.lenv * LEnv.lenv * expr) option
type itrace = choice list

(** Convert a [choice] to a [string]. *)
val show_choice : env -> choice -> string

(** Convert a [itrace] to a [string]. *)
val show_itrace : env -> itrace -> string

(** [dlink] stands for deep linking, and implements the deep interaction phase
    à la Chaudhuri for intuitionistic logic.
    The list of rules and explanations are available in :
        "A Drag-and-Drop Proof Tactic"
        http://www.lix.polytechnique.fr/Labo/Pablo.DONATO/papers/cpp-article.pdf *)
val dlink : link -> Form.Subst.subst * Form.Subst.subst -> Proof.proof -> Proof.subgoal * itrace
