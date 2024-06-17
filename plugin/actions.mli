(** This module defines the logic to carry out the effects of an actema action in Coq.
    It uses standard Coq tactics for simple actions such as introduction or induction, 
    and calls custom Ltac tactics (written by Benjamin Werner, see file theories/HOL.v) 
    for more complex actions such as DnD actions. *)

open Api
open Proofview

(** Contains the unsupported action and a short error message. *)
exception UnsupportedAction of Logic.action * string

(** Execute a single action. 
    The integer is the index of the subgoal the action takes place in.
    
    To execute a list of actions in order consider using [PVMonad.mapM_ execute]. *)
val execute : int * Logic.action -> unit tactic
