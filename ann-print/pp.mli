(**************************************************************************************)

open Tyxml

(* The abstract type of 'a docs, which is polymorphic over the type of annotations. *)
type 'annot doc

(**************************************************************************************)
(** Basic combinators. *)

(** [empty] is the empty document. *)
val empty : 'a doc

(** [char c] is an atomic document that consists of the single character [c].
    This character must not be a newline character. *)
val char : char -> 'a doc

(** [string s] is an atomic document that consists of the string [s]. This
    string must not contain a newline. The printing engine assumes that the
    ideal width of this string is [String.length s]. This assumption is safe
    if this is an ASCII string. Otherwise, {!fancystring} or {!utf8string}
    should be preferred. *)
val string : string -> 'a doc

(** [fancystring s alen] is an atomic document that consists of the string
    [s]. This string must not contain a newline. The string may contain fancy
    characters: color escape characters, UTF-8 characters, etc. Thus, its
    apparent length (which measures how many columns the text will take up on
    screen) differs from its length in bytes. The printing engine assumes
    that its apparent length is [alen]. *)
val fancystring : string -> int -> 'a doc

(** [utf8string s] is an atomic document that consists of the UTF-8-encoded
    string [s]. This string must not contain a newline. [utf8string s] is
    equivalent to [fancystring s (utf8_length s)], where [utf8_length s] is
    the apparent length of the UTF-8-encoded string [s]. *)
val utf8string : string -> 'a doc

(** The atomic document [hardline] represents a forced newline. This document
    has infinite ideal width: thus, if there is a choice between printing it
    in flat mode and printing it in normal mode, normal mode is preferred. In
    other words, when [hardline] is placed directly inside a group, this
    group is dissolved: [group hardline] is equivalent to [hardline]. This
    combinator should be seldom used; consider using {!break} instead. *)
val hardline : 'a doc

(** The atomic document [blank n] consists of [n] blank characters. A blank
    character is like an ordinary ASCII space character [char ' '], except
    that blank characters that appear at the end of a line are automatically
    suppressed. *)
val blank : int -> 'a doc

(** [space] is a synonym for [blank 1]. It consists of one blank character.
    It is therefore not equivalent to [char ' ']. *)
val space : 'a doc

(** The document [break n] is a breakable blank of width [n]. It produces [n]
    blank characters if the printing engine is in flat mode, and a single
    newline character if the printing engine is in normal mode. [break 1] is
    equivalent to [ifflat (blank 1) hardline]. *)
val break : int -> 'a doc

(** [doc1 ^^ doc2] is the concatenation of the documents [doc1] and [doc2]. *)
val ( ^^ ) : 'a doc -> 'a doc -> 'a doc

(** [group doc] encodes a choice. If the document [doc] fits on the current
    line, then it is rendered on a single line, in flat mode. (All [group]
    combinators inside it are then ignored.) Otherwise, this group is
    dissolved, and [doc] is rendered in normal mode. There might be more
    groups within [doc], whose presence leads to further choices being
    explored. *)
val group : 'a doc -> 'a doc

(** [ifflat doc1 doc2] is rendered as [doc1] if the printing engine is in
    flat mode, that is, if the printing engine has determined that some
    enclosing group fits on the current line. Otherwise, it is rendered as
    [doc2]. Use this combinator with caution! Because the printing engine is
    free to choose between [doc1] and [doc2], these documents must be
    semantically equivalent. It is up to the user to enforce this property. *)
val ifflat : 'a doc -> 'a doc -> 'a doc

(** To render the document [nest j doc], the printing engine temporarily
    increases the current indentation level by [j], then renders [doc]. The
    effect of the current indentation level is as follows: every time a
    newline character is emitted, it is immediately followed by [n] blank
    characters, where [n] is the current indentation level. Thus, one may
    think of [nest j doc] roughly as the document [doc] in which [j] blank
    characters have been inserted after every newline character. *)
val nest : int -> 'a doc -> 'a doc

(** To render [align doc], the printing engine sets the current indentation
    level to the current column, then renders [doc]. In other words, the
    document [doc] is rendered within a box whose upper left corner is the
    current position of the printing engine. *)
val align : 'a doc -> 'a doc

(** [annotate ann doc] is rendered as [doc], surrounded by the annotation [ann].
    The meaning of annotations is backend-dependent (see below). *)
val annotate : 'a -> 'a doc -> 'a doc

(**************************************************************************************)
(** Higher-level combinators. *)

(** [repeat n doc] is the document obtained by concatenating [n] copies of
    the document [doc]. *)
val repeat : int -> 'a doc -> 'a doc

(** [concat docs] is the concatenation of the documents in the list [docs]. *)
val concat : 'a doc list -> 'a doc

(** [separate sep docs] is the concatenation of the documents in the list
    [docs]. The separator [sep] is inserted between every two adjacent documents. *)
val separate : 'a doc -> 'a doc list -> 'a doc

(** [optional f None] is the empty document. [optional f (Some x)] is
    the document [f x]. *)
val optional : ('a -> 'a doc) -> 'a option -> 'a doc

(** [hang n doc] is analogous to [align], but additionally indents all lines,
    except the first one, by [n]. Thus, the text in the box forms a hanging
    indent. *)
val hang : int -> 'a doc -> 'a doc

(** [prefix n b left right] has the following flat layout:
    {[
      left right
    ]}
    and the following non-flat layout:
    {[
      left
        right
    ]}
    The parameter [n] controls the nesting of [right] (when not flat).
    The parameter [b] controls the number of spaces between [left] and [right]
    (when flat). *)
val prefix : int -> int -> 'a doc -> 'a doc -> 'a doc

(**[infix n b middle left right] has the following flat layout:
   {[
     left middle right
   ]}
   and the following non-flat layout:
   {[
     left middle
       right
   ]}
   The parameter [n] controls the nesting of [right] (when not flat).
   The parameter [b] controls the number of spaces between [left] and [middle]
   (always) and between [middle] and [right] (when flat). *)
val infix : int -> int -> 'a doc -> 'a doc -> 'a doc -> 'a doc

(** [flow sep docs] separates the documents in the list [docs] with the
    separator [sep] and arranges for a new line to begin whenever a document
    does not fit on the current line. This is useful for typesetting
    free-flowing, ragged-right text. A typical choice of [sep] is [break b],
    where [b] is the number of spaces that must be inserted between two
    consecutive words (when displayed on the same line). *)
val flow : 'a doc -> 'a doc list -> 'a doc

(** [flow_map sep f docs] is equivalent to [flow sep (List.map f docs)]. *)
val flow_map : 'a doc -> ('a -> 'a doc) -> 'a list -> 'a doc

(** [x ^+^ y] separates [x] and [y] with a non-breakable space.
    It is a short-hand for [x ^^ space ^^ y]. *)
val ( ^+^ ) : 'a doc -> 'a doc -> 'a doc

(** [x ^/^ y] is a short-hand for [prefix 0 1 x y]. 
    
    It has the following flat layout : 
    {[
      x y
    ]} 
    and the following non-flat layout : 
    {[
      x 
      y
    ]} *)
val ( ^/^ ) : 'a doc -> 'a doc -> 'a doc

(** [x ^//^ y] is a short-hand for [prefix 2 1 x y]. 
    
    It has the following flat layout : 
    {[
      x y
    ]} 
    and the following non-flat layout : 
    {[
      x 
        y
    ]} *)
val ( ^//^ ) : 'a doc -> 'a doc -> 'a doc

(**************************************************************************************)
(** Backends. *)

(** The pretty-printer works with an abstract backend.
    This is essentially a small imperative state machine. *)
module type Backend = sig
  (** The annotations supported by this backend. *)
  type annot

  (** The mutable state maintained by the backend. 
      This could be for instance a string buffer. *)
  type state

  (** The output type of the backend. This could be for instance a string. *)
  type output

  (** Create an initial state. *)
  val initial_state : unit -> state

  (** Extract an [output] from a [state]. This should not modify [state].
      It is assumed that we finished pretty-printing to [state]. *)
  val get_output : state -> output

  (** Output a single char. *)
  val add_char : state -> char -> unit

  (** Output a substring of the given string. *)
  val add_substring : state -> string -> ofs:int -> len:int -> unit

  (** From the point of view of the backend annotations form a stack.
      For instance nesting annotations [a] and [b] is handled by :
      - entering [a]
      - entering [b]
      - printing the contents of [b]
      - exiting [b]
      - exiting [a]
  *)

  (** Enter a new annotation scope. *)
  val enter_annot : state -> annot -> unit

  (** Exit the most recently entered annotation scope. *)
  val exit_annot : state -> annot -> unit
end

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

(**************************************************************************************)
(** Pretty-printing to a backend. *)

(** Instantiate the actual printer for a backend. 
    The pretty-printer can print a document to any backend that supports the right annotations.
    For instance we can build a document once and print it using several backends. *)
module Make (B : Backend) : sig
  (* Pretty print a document using the backend. *)
  val pp : width:int -> B.annot doc -> B.output
end
