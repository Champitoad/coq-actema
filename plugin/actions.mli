(** This module defines the logic to carry out the effects of an actema action in Coq.
    It uses predefined Coq tactics for simple actions, and calls custom Ltac tactics
    (written by Benjamin Werner, see folder theories/) for more complex actions
    such as DnD actions. *)

open Api
open Proofview

exception UnsupportedAction of Logic.action
exception UnexpectedDnD
exception InvalidPath of Logic.ipath

(** Contains the lemma name and an error message. *)
exception InvalidLemma of string * string

(** Execute a single action. The integer is the index of the subgoal the action takes place in. *)
val execute : int * Logic.action -> unit tactic

(** Convenience function to execute a list of actions, in order. *)
val execute_list : (int * Logic.action) list -> unit tactic
