open Fo

exception UnsupportedAction of CoreLogic.action_type

val export_action : Hidmap.hidmap -> Proof.proof -> CoreLogic.action -> Api.Logic_t.action
