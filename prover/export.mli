(*open Fo

  exception UnsupportedAction of Actions.action_type

  (** Export an Actema action to an API action.
      The handle parameter is the handle of the subgoal the action acts on.
      This can perform some amount deep interaction between subformulas. *)
  val export_action :
       Hidmap.hidmap
    -> Proof.proof
    -> Handle.t * Actions.action_type
    -> Api.Logic.action
*)
