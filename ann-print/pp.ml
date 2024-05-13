open Tyxml

(**************************************************************************************)
(** Width requirements. *)

(* A type of integers with infinity. *)
type requirement = int (* with infinity *)

(* Infinity is encoded as [max_int]. *)
let infinity : requirement = max_int

(* Addition of integers with infinity. *)
let ( ++ ) (x : requirement) (y : requirement) : requirement =
  if x = infinity || y = infinity then infinity else x + y

(* Comparison of requirements is just ordinary comparison. *)

(**************************************************************************************)
(** Documents and combinators. *)

(** The type of documents. This is a GADT, but the only constructor that actually 
    uses the type parameter is [Annot]. *)
type _ doc =
  (* [Empty] is the empty document. *)
  | Empty : 'a doc
  (* [FancyString (s, ofs, len, apparent_length)] is a (portion of a) string
     that may contain fancy characters: color escape characters, UTF-8 or
     multi-byte characters, etc. Thus, the apparent length (which corresponds
     to what will be visible on screen) differs from the length (which is a
     number of bytes, and is reported by [String.length]). We assume, but do
     not check, that fancystrings do not contain a newline character. *)
  | FancyString : string * int * int * int -> 'a doc
  (* [Blank n] is a document that consists of [n] blank characters. *)
  | Blank : int -> 'a doc
  (* When in flattening mode, [IfFlat (d1, d2)] turns into the document
     [d1]. When not in flattening mode, it turns into the document [d2]. *)
  | IfFlat : 'a doc * 'a doc -> 'a doc
  (* When in flattening mode, [HardLine] causes a failure, which requires
     backtracking all the way until the stack is empty. When not in flattening
     mode, it represents a newline character, followed with an appropriate
     number of indentation. A common way of using [HardLine] is to only use it
     directly within the right branch of an [IfFlat] construct. *)
  | HardLine
  (* The following constructors store their space requirement. This is the
     document's apparent length, if printed in flattening mode. This
     information is computed in a bottom-up manner when the document is
     constructed.

     In other words, the space requirement is the number of columns that the
     document needs in order to fit on a single line. We express this value in
     the set of `integers extended with infinity', and use the value
     [infinity] to indicate that the document cannot be printed on a single
     line.

     Storing this information at [Group] nodes is crucial, as it allows us to
     avoid backtracking and buffering.

     Storing this information at other nodes allows the function [requirement]
     to operate in constant time. This means that the bottom-up computation of
     requirements takes linear time.

     [Cat (req, doc1, doc2)] is the concatenation of the documents [doc1] and
     [doc2]. The space requirement [req] is the sum of the requirements of
     [doc1] and [doc2]. *)
  | Cat : requirement * 'a doc * 'a doc -> 'a doc
  (* [Nest (req, j, doc)] is the document [doc], in which the indentation
     level has been increased by [j], that is, in which [j] blanks have been
     inserted after every newline character. The space requirement [req] is
     the same as the requirement of [doc]. *)
  | Nest : requirement * int * 'a doc -> 'a doc
  (* [Group (req, doc)] represents an alternative: it is either a flattened
     form of [doc], in which occurrences of [Group] disappear and occurrences
     of [IfFlat] resolve to their left branch, or [doc] itself. The space
     requirement [req] is the same as the requirement of [doc]. *)
  | Group : requirement * 'a doc -> 'a doc
  (* [Align (req, doc)] increases the indentation level to reach the current
     column.  Thus, the document [doc] is rendered within a box whose upper
     left corner is the current position. The space requirement [req] is the
     same as the requirement of [doc]. *)
  | Align : requirement * 'a doc -> 'a doc
    (* [Annot (req, ann, doc)] annotates the document [doc] with annotation [ann].
       The space requirement [req] is the same as the requirement of [doc]. *)
  | Annot : requirement * 'a * 'a doc -> 'a doc

(** Retrieving or computing the space requirement of a doc.
    This is constant-time. *)
let rec requirement = function
  | Empty -> 0
  | FancyString (_, _, _, len) -> len
  | Blank len -> len
  | IfFlat (doc1, _) -> requirement doc1
  | HardLine -> infinity
  | Cat (req, _, _) -> req
  | Nest (req, _, _) -> req
  | Group (req, _) -> req
  | Align (req, _) -> req
  | Annot (req, _, _) -> req

let empty = Empty

let fancysubstring s ofs len apparent_length =
  if len = 0 then empty else FancyString (s, ofs, len, apparent_length)

let fancystring s apparent_length = fancysubstring s 0 (String.length s) apparent_length

let utf8_length s =
  let rec length_aux s c i =
    if i >= String.length s
    then c
    else
      let n = Char.code (String.unsafe_get s i) in
      let k = if n < 0x80 then 1 else if n < 0xe0 then 2 else if n < 0xf0 then 3 else 4 in
      length_aux s (c + 1) (i + k)
  in
  length_aux s 0 0

let utf8string s = fancystring s (utf8_length s)
let string s = fancystring s (String.length s)

let char c =
  assert (c <> '\n');
  fancystring (String.make 1 c) 1

let space = FancyString (" ", 0, 1, 1)
let hardline = HardLine
let blank n = match n with 0 -> empty | 1 -> space | _ -> Blank n
let ifflat doc1 doc2 = match doc1 with IfFlat (doc1, _) | doc1 -> IfFlat (doc1, doc2)
let break i = ifflat (blank i) hardline

let ( ^^ ) x y =
  match (x, y) with
  | Empty, _ -> y
  | _, Empty -> x
  | _, _ -> Cat (requirement x ++ requirement y, x, y)

let nest i x =
  assert (i >= 0);
  Nest (requirement x, i, x)

let group x =
  let req = requirement x in
  if req = infinity then x else Group (req, x)

let align x = Align (requirement x, x)
let annotate ann x = Annot (requirement x, ann, x)

(*** A variant of [fold_left] that keeps track of the element index. *)
let foldli (f : int -> 'b -> 'a -> 'b) (acc : 'b) (xs : 'a list) : 'b =
  let r = ref 0 in
  List.fold_left
    (fun acc x ->
      let i = !r in
      r := i + 1;
      f i acc x)
    acc xs

let repeat n doc =
  let rec loop n acc = if n = 0 then acc else loop (n - 1) (doc ^^ acc) in
  loop n empty

let concat docs =
  (* We take advantage of the fact that [^^] operates in constant
     time, regardless of the size of its arguments. The document
     that is constructed is essentially a reversed list (i.e., a
     tree that is biased towards the left). This is not a problem;
     when pretty-printing this document, the engine will descend
     along the left branch, pushing the nodes onto its stack as
     it goes down, effectively reversing the list again. *)
  List.fold_left ( ^^ ) empty docs

let separate sep docs =
  foldli (fun i accu doc -> if i = 0 then doc else accu ^^ sep ^^ doc) empty docs

let hang i d = align (nest i d)
let optional f = function None -> empty | Some x -> f x
let[@inline] ( ^+^ ) x y = x ^^ space ^^ y
let prefix n b x y = group (x ^^ nest n (break b ^^ y))
let[@inline] ( ^/^ ) x y = prefix 0 1 x y
let[@inline] ( ^//^ ) x y = prefix 2 1 x y
let infix n b op x y = prefix n b (x ^^ blank b ^^ op) y

let flow_map sep f docs =
  foldli
    (fun i accu doc ->
      if i = 0
      then f doc
      else
        accu
        ^^ (* This idiom allows beginning a new line if [doc] does not
              fit on the current line. *)
        group (sep ^^ f doc))
    empty docs

let flow sep docs = flow_map sep (fun x -> x) docs

(**************************************************************************************)
(** Backends *)

module type Backend = sig
  type annot
  type output
  type state

  val initial_state : unit -> state
  val get_output : state -> output
  val add_char : state -> char -> unit
  val add_substring : state -> string -> ofs:int -> len:int -> unit
  val enter_annot : state -> annot -> unit
  val exit_annot : state -> annot -> unit
end

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

(**************************************************************************************)
(** Pretty-printing to a backend. *)

module Make (B : Backend) = struct
  (* Printing blank space (indentation characters). *)

  let blank_length = 80
  let blank_buffer = String.make blank_length ' '

  let rec blanks channel n =
    if n <= 0
    then ()
    else if n <= blank_length
    then B.add_substring channel blank_buffer ~ofs:0 ~len:n
    else begin
      B.add_substring channel blank_buffer ~ofs:0 ~len:blank_length;
      blanks channel (n - blank_length)
    end

  (* The internal state maintained by the rendering engine. *)
  type state =
    { (* The line width. *)
      width : int
    ; (* The current column. *)
      mutable column : int
    ; (* The output channel. *)
      channel : B.state
    }

  (* For simplicity, the rendering engine is NOT in tail-recursive style. *)
  let rec pretty state (indent : int) (flatten : bool) doc =
    match doc with
    | Empty -> ()
    | FancyString (s, ofs, len, apparent_length) ->
        B.add_substring state.channel s ~ofs ~len;
        state.column <- state.column + apparent_length
    | Blank n ->
        blanks state.channel n;
        state.column <- state.column + n
    | HardLine ->
        assert (not flatten);
        B.add_char state.channel '\n';
        blanks state.channel indent;
        state.column <- indent
    | IfFlat (doc1, doc2) -> pretty state indent flatten (if flatten then doc1 else doc2)
    | Cat (_, doc1, doc2) ->
        pretty state indent flatten doc1;
        pretty state indent flatten doc2
    | Nest (_, j, doc) -> pretty state (indent + j) flatten doc
    | Group (req, doc) ->
        let flatten = flatten || state.column ++ req <= state.width in
        pretty state indent flatten doc
    | Align (_, doc) -> pretty state state.column flatten doc
    | Annot (_, ann, doc) ->
        B.enter_annot state.channel ann;
        pretty state indent flatten doc;
        B.exit_annot state.channel ann

  let pp ~width doc =
    let channel = B.initial_state () in
    pretty { width; column = 0; channel } 0 false doc;
    B.get_output channel
end
