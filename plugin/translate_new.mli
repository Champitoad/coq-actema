(** This module deals translates Coq goals into Actema goals. *)

open Api_new
open CoqUtils

(** Translate a Coq goal to an Actema goal. This includes : 
    - Translating the conclusion. 
    - Translating the hypotheses and variables. 
    - Building the environment needed to type the goal. *)
val translate_goal : Goal.t -> Logic.pregoal
