(** This module defines functions to manipulate the lemma database. *)

open CoreLogic


(** Filter the lemma database by keeping only the lemmas that have a dnd interaction with a given selection. 
    This only changes the lemma database. *)
val filter_by_selection : IPath.t -> Proof.proof -> Proof.proof

(** Filter the lemma database by keeping only the lemmas whose name matches a given pattern.
    This only changes the lemma database.  *)
val filter_by_name : string -> Proof.proof -> Proof.proof
    