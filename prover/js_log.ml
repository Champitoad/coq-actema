(** This module will log messages to the Javascript console. 

    You should use this module instead of [Format] or [Printf] to log
    messages from the prover (or else the messages might not get displayed). *)

open Js_of_ocaml

(** Print an (Ocaml) string. A newline is added automatically. *)
let log (s : string) : unit = Firebug.console##log (Js.string s)

(** Same as [log], but logs an arbitrary javascript object. *)
let log_object (obj : 'a Js.t) : unit = Firebug.console##log obj
