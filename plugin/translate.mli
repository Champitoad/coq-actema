(** This module translates Coq term into Actema terms. *)

open Api_new
open CoqUtils
open Lang

(** Translate a Coq term to an Actema term. 
    Also returns the environment needed to type the term. *)
val econstr : Goal.t -> EConstr.t -> Term.t * Env.t

(** Translate a Coq goal to an Actema goal. This includes : 
    - Translating the conclusion. 
    - Translating the hypotheses and variables. 
    - Building the environment needed to type the goal. *)
val goal : Goal.t -> Logic.pregoal

(** Translate all the lemmas we can to Actema, along with 
    the environment needed to type them. *)
val lemmas : Goal.t -> Logic.lemma list * Env.t
