open Api
open Proofview

(** Export all the lemmas we can translate to actema, 
    along with their environment. *)
val export_lemmas : unit -> (Logic.lemma list * Logic.env) tactic

(** Do a pre-selection of lemmas, according to a name pattern. *)
val preselect_lemmas_name : string -> Logic.lemma list -> Logic.lemma list

(** Do a pre-selection of lemmas, according to a selected subterm. *)
val preselect_lemmas_selection : Logic.term -> Logic.lemma list -> Logic.lemma list
