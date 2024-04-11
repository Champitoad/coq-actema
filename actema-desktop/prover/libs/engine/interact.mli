open Link
open Fo

type choice = int * (LEnv.lenv * LEnv.lenv * expr) option
type itrace = choice list

(** Convert a [choice] to a [string]. *)
val show_choice : env -> choice -> string

(** Convert a [itrace] to a [string]. *)
val show_itrace : env -> itrace -> string

(** [dlink] stands for _d_eep linking, and implements the deep interaction phase
    à la Chaudhuri for intuitionistic logic. *)
val dlink : link -> Form.Subst.subst * Form.Subst.subst -> Proof.proof -> Proof.subgoal * itrace
