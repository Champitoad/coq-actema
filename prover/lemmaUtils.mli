(** This module defines functions to manipulate the lemma database. *)

open Api
open Logic
open ProverLogic

(** Filter the lemma database by keeping only the lemmas that match the given name and selection. 
    This only changes the lemma database.  *)
val filter : string option -> Path.t option -> Proof.t -> Proof.t
