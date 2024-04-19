(** This module defines the logic to carry out the effects of an actema action in Coq.
    It uses predefined Coq tactics for simple actions, and calls custom Ltac tactics
    (written by Benjamin Werner, see folder theories/) for more complex actions
    such as DnD actions. *)

open Api
open Proofview

(** Contains the unsupported action and a short error message. *)
exception UnsupportedAction of Logic.action * string

exception UnexpectedDnD
exception InvalidPath of Logic.ipath

(** Execute a single action. The integer is the index of the subgoal the action takes place in. *)
val execute : int * Logic.action -> unit tactic

(** Convenience function to execute a list of actions, in order. *)
val execute_list : (int * Logic.action) list -> unit tactic
