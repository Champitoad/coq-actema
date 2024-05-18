(* This file defines the HTTP protocol used to communicate between
   the plugin (http client) and the frontend (http server). *)
open Api
open Lang

exception ActemaError of string
exception UnsupportedRequestMethod of string
exception UnsupportedHttpResponseCode of int

(** The plugin sends the goals (in API format) to the frontend, 
    which sends back an action. *)
type action =
  | Do of int * Logic.action
  | Done
  | Undo
  | Redo
  | Lemmas of string option * Term.t option
      (** The frontend asks the plugin for a list of lemmas.
          The parameters are used to perform a pre-selection of lemmas : 
          - The string is a pattern to match against the lemma name.
          - The term is the selected subterm. It can have free variables. *)

(** Tell the frontend that the proof is complete, and receive an (empty) response. *)
val send_qed : unit -> unit Lwt.t

(** Send the goals to the frontend, and receive an action as response. *)
val send_goals : Logic.goal list -> action Lwt.t

(** Send a set of lemmas to the frontend, and receive an action as response. *)
val send_lemmas : Logic.lemma list -> Env.t -> action Lwt.t

(** Tell the frontend that an error occured in the plugin,
    and receive an (empty) response. *)
val send_error : string -> unit Lwt.t
