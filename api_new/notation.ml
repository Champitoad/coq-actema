open Lang
open Tyxml
open Ann_print

(***************************************************************************************)
(** Instantiate the pretty-printing library. *)

type annot = Pp.XmlBackend.annot

module PpXml = Pp.Make (Pp.XmlBackend)

module PpString = Pp.Make (Pp.StringBackend (struct
  type t = annot
end))

(***************************************************************************************)
(** Actual pretty-printing *)

let pp_term (env : Env.t) (t : Term.t) : annot Pp.doc = Pp.empty

(***************************************************************************************)
(** Backend-specific code. *)

let term_to_string ?(width = 40) env t : string =
  assert (0 <= width);
  PpString.pp ~width (pp_term env t)

let term_to_xml ?(width = 40) env t : Xml.elt =
  assert (0 <= width);
  Xml.node "span" @@ PpXml.pp ~width (pp_term env t)
