(** This is the main entry point of the Coq plugin. *)

open Proofview

(** The main actema tactic.

    If the [force] flag is set, we start an interactive proof regardless of whether 
    there is already a saved proof. If [force] is not set we use the saved proof if it exists. *)
val actema_tac : ?force:bool -> string -> unit tactic

(** A test tactic, for debug purposes only. *)
val test_tac : unit -> unit tactic
