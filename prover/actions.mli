(** This module implements the logic to search for all valid actions (DnD but not only)
    on a given subgoal. 
    
    This is notably used to implement the "highlighting" feature : 
    when the user starts dragging an item (for instance a hypothesis), 
    the frontend will highlight all the places where dropping the item makes sense. *)

open CoreLogic
open Fo

type asource = { kind : asource_kind; selection : selection }
and asource_kind = [ `Click of IPath.t | `DnD of adnd | `Ctxt ]
and adnd = { source : IPath.t; destination : IPath.t option }
and selection = IPath.t list

type osource = [ `Click of IPath.t | `DnD of Link.link | `Ctxt ]

type action_type =
  [ `Intro of int
  | `Elim of Handle.t * int
  | `Lemma of name
  | `Ind of Handle.t
  | `Simpl of IPath.t
  | `Red of IPath.t
  | `Indt of IPath.t
  | `Case of IPath.t
  | `Pbp of IPath.t
  | `Fold of vname
  | `Unfold of vname
  | `Hyperlink of Link.hyperlink * Link.linkaction list ]

(** An action consists in :
      - The index of the goal its acts on. 
      - The action type. *)
type action = Handle.t * action_type

type aoutput =
  { description : string
  ; icon : string option
  ; highlights : IPath.t list
  ; kind : osource
  ; action : action
  }

(** Get the list of all valid actions on a given proof state. *)
val actions : Proof.proof -> asource -> aoutput list
