(** This module implements the logic to search for all valid actions (DnD but not only)
    on a given subgoal. 
    
    This is notably used to implement the "highlighting" feature : 
    when the user starts dragging an item (for instance a hypothesis), 
    the frontend will highlight all the places where dropping the item makes sense. *)

open Api
open Logic
open ProverLogic

(** An [action_kind] discriminates between :
    - [Click path] where the user clicked on [path].
    - [Ctxt] where the user clicked on an item in the contextual (circle-shaped) menu.
    - [Dnd source destination] where the user is dragging [source], optionally on top of [destination]. *)
type akind = Click of Path.t | DnD of Path.t * Path.t option | Ctxt
[@@deriving show]

(** An action source. From this and a [Proof.t] we should be able to generate all valid actions. *)
type asource = { kind : akind; selection : Path.t list } [@@deriving show]

(** An action output. 

    This contains information useful or the frontend such as :
    - [description] : a text string that consisely describes the action.
    - [icon] : the name of a FontAwesome icon to display.
    - [highlights] : a set of paths to highlight.
    
    It also contains proof-related information :
    - [kind] : the action kind.
    - [goal_id] : the identifier of the goal this action executes in.
    - [action] : the corresponding Actema action. *)
type aoutput =
  { description : string
  ; icon : string option
  ; highlights : Path.t list
  ; kind : akind
  ; goal_id : int
  ; action : Logic.action
  }
[@@deriving show]

(** [actions proof source] gets the list of all valid actions on [proof] with 
    source [source]. *)
val actions : Proof.t -> asource -> aoutput list
