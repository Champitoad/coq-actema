(** This module implements the logic to search for all valid actions (DnD but not only)
    on a given subgoal. 
    
    This is notably used to implement the "highlighting" feature : 
    when the user starts dragging an item (for instance a hypothesis), 
    the frontend will highlight all the places where dropping the item makes sense. *)

open Utils.Pervasive
open Api
open Logic
open Lang
open ProverLogic

(** An [action_kind] discriminates between :
    - [Click path] where the user clicked on [path].
    - [Ctxt] where the user clicked on an item in the contextual (circle-shaped) menu.
    - [Dnd source destination] where the user is dragging [source], optionally on top of [destination]. *)
type akind = Click of Path.t | DnD of Path.t * Path.t option | Ctxt
[@@deriving show]

(** An action source. From this and a [Proof.t] we should be able to generate all valid actions. *)
type asource = { kind : akind; selection : Path.t list } [@@deriving show]

(** A [preaction] is similar to an Actema action [Logic.action], but it contains 
    a bit less information (for instance for hyperlinks). *)
type preaction =
  (* Trivially solve the goal with a hypothesis. *)
  | Exact of Name.t
  (* Apply an introduction rule on the conclusion.
     The [int] indicates which intro rule to use in case of ambiguity
     (for instance when the goal is a disjunction). *)
  | Intro of int
  (* Apply an elimination rule on a hypothesis.
     The name identifies the hypothesis we are eliminating.
     The [int] indicates which intro rule to use in case of ambiguity
     (for instance when the hypothesis is an equality, it indicates in which direction to rewrite) *)
  | Elim of Name.t * int
  (* Simplify the subterm pointed at by a path. *)
  | Simpl of Path.t
  | Case of Term.t
  | Ind of Term.t
  (* Fold all occurences of a local variable. *)
  | Fold of Name.t
  (* Unfold all occurences of a local variable. *)
  | Unfold of Name.t
    (*| Ind of int
      | Simpl of Path.t
      | Red of Path.t
      | Indt of Path.t
      | Case of Path.t
      | Pbp of Path.t*)
  | Hyperlink of Link.hyperlink * Link.linkaction list
[@@deriving show]

(** An action output. 

    This contains information useful or the frontend such as :
    - [description] : a text string that consisely describes the action.
    - [icon] : the name of a FontAwesome icon to display.
    - [highlights] : a set of paths to highlight.
    
    It also contains proof-related information :
    - [kind] : the action kind.
    - [goal_id] : the identifier of the goal this action executes in.
    - [preaction] : the corresponding preaction. *)
type aoutput =
  { description : string
  ; icon : string option
  ; highlights : Path.t list
  ; kind : akind
  ; goal_id : int
  ; preaction : preaction
  }
[@@deriving show]

(** [actions proof source] gets the list of all valid actions on [proof] with 
    source [source]. *)
val actions : Proof.t -> asource -> aoutput list
