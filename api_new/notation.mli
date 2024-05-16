(** This module handles pretty-printing of terms to string/xml. *)

open Lang
open Tyxml

(** [term_to_string ~width ~ctx env t] pretty-prints the term [t] to a string. 
    [ctx] is the context of free variables of [t], and is empty by default.
    It uses the pretty-printing information contained in the environment. 
    It tries to print a string with width at most [width]. *)
val term_to_string : ?width:int -> ?ctx:Context.t -> Env.t -> Term.t -> string

(** [term_to_xml ~width env t] pretty-prints the term [t] to an xml element. 
    [ctx] is the context of free variables of [t], and is empty by default.
    This is meant to be used by the frontend. *)
val term_to_xml : ?width:int -> ?ctx:Context.t -> Env.t -> Term.t -> Xml.elt
