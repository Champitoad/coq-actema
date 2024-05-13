(** This module defines a few example backends. *)

open Pp
open Tyxml

(** This backend outputs raw strings, and ignores all annotations. 
    Internally it uses a string buffer. *)
module StringBackend (A : sig
  type t
end) : Backend with type annot = A.t and type output = string

(** This backend generates Xml elements.
      
    It supports annotations [(tag, attribs)] which wrap their content in an Xml node/leaf 
    (depending on whether the content is empty or not) with tag [tag] and attributes [attribs].
*)
module XmlBackend :
  Backend with type annot = string * Xml.attrib list and type output = Xml.elt list
