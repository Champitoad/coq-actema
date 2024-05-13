(** This module handles pretty-printing terms to string/xml. *)

open Lang
open Tyxml

(** [term_to_string ~width env t] pretty-prints the term [t] to a string. 
    It uses the pretty-printing information contained in the environment. 
    It tries to print a string with width at most [width]. *)
val term_to_string : ?width:int -> Env.t -> Term.t -> string

(** [term_to_xml ~width env t] pretty-prints the term [t] to an xml element. 
    This is meant to be used by the frontend. *)
val term_to_xml : ?width:int -> Env.t -> Term.t -> Xml.elt
