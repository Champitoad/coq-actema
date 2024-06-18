(* This module defines the HTTP protocol used to communicate between
   the plugin (http client) and the frontend (http server). *)

open Api
open Lang

exception ActemaError of string
exception UnsupportedRequestMethod of string
exception UnsupportedHttpResponseCode of int

(** The plugin sends the goals to the frontend, 
    which sends back an action. *)
type action =
  (* The user made an action in the frontend (e.g. a drag-and-drop).
     The [int] argument is the index of the subgoal the action takes places in. *)
  | Do of int * Logic.action
  (* The user is finished in Actema. This does not mean that the proof is complete :
     the user may continue the proof using e.g. Ltac. *)
  | Done
  (* Undo the last Actema action. *)
  | Undo
  (* Redo the last undone Actema action. *)
  | Redo
  (* The prover requested for the plugin to send the list of (all) lemmas.

     We only do this on request (and not by default) because sending the lemmas
     over HTTP and then parsing them in the prover can take a bit of time (around 1 second).
     This delay would be a bit annoying if it happened on every actema action. *)
  | Lemmas

(** Tell the frontend that the proof is complete, and receive an (empty) response. *)
val send_qed : unit -> unit Lwt.t

(** Send the goals to the frontend, and receive an action as response. *)
val send_goals : Logic.goal list -> action Lwt.t

(** Send a set of lemmas to the frontend, and receive an action as response. *)
val send_lemmas : Logic.lemma list -> Env.t -> action Lwt.t

(** Tell the frontend that an error occured in the plugin,
    and receive an (empty) response. *)
val send_error : string -> unit Lwt.t
