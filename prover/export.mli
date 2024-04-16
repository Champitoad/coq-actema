open Fo

exception UnsupportedAction of Link.action_type

(** Export an Actema action to an API action. 
    This can perform some amount deep interaction between subformulas. *)
val export_action : Hidmap.hidmap -> Proof.proof -> Link.action -> Api.Logic_t.action
