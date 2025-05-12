(** This module will log messages to the Javascript console. 

    You should use this module instead of [Format] or [Printf] to log
    messages from the prover (or else the messages might not get displayed). *)

open Js_of_ocaml

(** Print an (Ocaml) string. A newline is added automatically. *)
let log (s : string) : unit = Js_of_ocaml.Console.console##log (Js.string s)

(** Print a formatted string. A newline is added automatically. *)
let printf fmt = Format.ksprintf log fmt

(** Same as [log], but logs an arbitrary javascript object. *)
let log_object (obj : 'a Js.t) : unit = Js_of_ocaml.Console.console##log obj
