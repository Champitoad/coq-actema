open Fo

exception UnsupportedAction of Actions.action_type

(** Export an Actema action to an API action. 
    This can perform some amount deep interaction between subformulas. *)
val export_action : Hidmap.hidmap -> Proof.proof -> Actions.action -> Api.Logic.action
