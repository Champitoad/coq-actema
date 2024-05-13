open Tyxml

module StringBackend (A : sig
  type t
end) =
struct
  type annot = A.t
  type state = Buffer.t
  type output = string

  let initial_state () = Buffer.create 256
  let get_output buffer = Buffer.contents buffer
  let add_char channel char = Buffer.add_char channel char
  let add_substring channel string ~ofs ~len = Buffer.add_substring channel string ofs len
  let enter_annot _channel _annot = ()
  let exit_annot _channel _annot = ()
end

module XmlBackend = struct
  type annot = string * Xml.attrib list
  type output = Xml.elt list

  (** The type of the  internal state is a little involved. It is a stack of [Xml.elt list].
      Each element of the stack corresponds to an annotation scope, i.e. to an Xml node 
      that has been opened but not yet closed. *)

  (** A frame on the stack can contain multiple Xml elements.
      The elements are in reverse order : the head of the list is the last Xml element. *)
  type frame = Xml.elt list

  (** The stack should never be empty. *)
  type state = frame Stack.t

  (** [modify_top stack f] applies the function [f] to the top frame of the stack. 
      This assumes the stack is nonempty. *)
  let modify_top stack f =
    let frame = Stack.pop stack in
    Stack.push (f frame) stack

  (** Initially the stack has a single frame, which is empty. *)
  let initial_state () =
    let stack = Stack.create () in
    Stack.push [] stack;
    stack

  (** In the final state, the stack should contain a single frame. *)
  let get_output stack =
    assert (Stack.length stack = 1);
    (* Don't forget to reverse the list of elements. *)
    List.rev @@ Stack.top stack

  (** Add a (sub)string to the current frame. *)
  let add_substring stack str ~ofs ~len =
    (* [Xml.pcdta] automatically escapes special characters (e.g. '<' or '>') to Xml entities.
       However it does not escape whitespace (spaces and newlines) : the resulting Xml has
       to be rendered with style="white-space: pre" to preserve whitespace. *)
    modify_top stack @@ fun frame -> Xml.pcdata (String.sub str ofs len) :: frame

  (** Add a single character to the current frame. *)
  let add_char stack char = add_substring stack (String.make 1 char) ~ofs:0 ~len:1

  (** Enter a new annotation scope, i.e. push a frame on the stack. *)
  let enter_annot stack _ = Stack.push [] stack

  (** Exit an annotation scope, i.e. pop the top stack frame. *)
  let exit_annot stack (tag, attribs) =
    assert (Stack.length stack > 1);
    (* Pop the current top frame and make an Xml node/leaf out of it. *)
    let children = List.rev @@ Stack.pop stack in
    let new_elt =
      if children = [] then Xml.leaf tag ~a:attribs else Xml.node tag ~a:attribs children
    in
    (* Add this Xml element to the new top frame. *)
    modify_top stack @@ fun frame -> new_elt :: frame
end
