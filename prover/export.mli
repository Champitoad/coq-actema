(** This module translates preactions [Actions.preaction] into real actions 
    [Logic.action]. The only interesting case is for linkactions, for which
    we need to perform deep interaction to choose an order for the interaction rules
    (see interactl.ml). *)

open Api
open ProverLogic

(** We can't export the given preaction to an API action. *)
exception UnsupportedAction of Actions.preaction

(** Export a preaction to an API action.
    The int parameter is the index of the subgoal the preaction acts on.
    
    For DnD actions this will perform deep interaction between the subformulas. *)
val export_action : Proof.t -> int -> Actions.preaction -> Logic.action
