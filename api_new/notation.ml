open Lang
open Tyxml
open Ann_print
module StringMap = Map.Make (String)

(***************************************************************************************)
(** Instantiate the pretty-printing library. *)

type annot = Pp.XmlBackend.annot

module PpXml = Pp.Make (Pp.XmlBackend)

module PpString = Pp.Make (Pp.StringBackend (struct
  type t = annot
end))

(***************************************************************************************)
(** Actual pretty-printing *)

let span ?(attribs = []) (x : annot Pp.doc) : annot Pp.doc =
  Pp.annotate ("span", attribs) x

let paren x =
  let open Pp in
  char '(' ^^ x ^^ char ')'

(** Get the formatting information for a name. *)
let name_info env name =
  match Name.Map.find_opt name env.Env.pp_info with
  | Some info -> info
  | None -> { symbol = Name.show name; position = `Prefix }

(** Pretty-print a global variable using its symbol. *)
let pp_global env name =
  let info = name_info env name in
  Pp.string info.symbol

(** Pretty-print a local variable. *)
let pp_local env name = Pp.string @@ Name.show name

(** Pretty-print a binder. *)
let pp_binder env name = Pp.string @@ Name.show name

(** [pp_term env path t] pretty-prints the term [t]. 
    The argument [path] keeps track of the path to the term [t], 
    and is used to annotate the Xml divs of each subterm. 
    Initially [path] should be empty. *)
let rec pp_term env path (t : Term.t) : annot Pp.doc =
  let open Pp in
  let content =
    match t with
    | Var name -> pp_local env name
    | Cst name -> pp_global env name
    | Sort `Prop -> string "Prop"
    | Sort `Type -> string "Type"
    | Lambda (name, ty, body) ->
        let pp_binder = string "fun" ^+^ pp_binder env name ^+^ string ":" in
        let pp_ty = pp_term env (0 :: path) ty ^+^ string "=>" in
        let pp_body = pp_term env (1 :: path) body in
        (pp_binder ^//^ pp_ty) ^//^ pp_body
    | Arrow (t1, t2) ->
        (* We might or might not need to add parentheses around [t1]. *)
        let pp_t1 =
          match t1 with
          | Var _ | Cst _ | App _ -> pp_term env (0 :: path) t1
          | _ -> paren @@ pp_term env (0 :: path) t1
        in
        (* We don't need parentheses around [t2]. *)
        let pp_t2 = pp_term env (1 :: path) t2 in
        (* Combine the results. *)
        (pp_t1 ^+^ string "->") ^/^ pp_t2
    | Prod (name, ty, body) ->
        let pp_binder = string "forall" ^+^ pp_binder env name ^+^ string ":" in
        let pp_ty = pp_term env (0 :: path) ty ^^ string "," in
        let pp_body = pp_term env (1 :: path) body in
        (pp_binder ^//^ pp_ty) ^//^ pp_body
    | App (f, args) ->
        (* Applications are a bit tricky : we have to check if the function is a constant,
           and if so take into account the formatting information about that constant. *)
        let elts =
          match f with
          | Cst name ->
              let info = name_info env name in
              begin
                match (info.position, args) with
                | `Prefix, args -> f :: args
                | `Infix, [ arg1; arg2 ] -> [ arg1; f; arg2 ]
                | `Suffix, [ arg ] -> [ arg; f ]
                | _ -> assert false
              end
          | _ -> f :: args
        in
        (* Pretty-print the applications one by one, adding parentheses where needed. *)
        elts
        |> List.mapi
             begin
               fun i (t : Term.t) ->
                 match t with
                 | Var _ | Cst _ -> pp_term env (i :: path) t
                 | _ -> paren @@ pp_term env (i :: path) t
             end
        |> flow (break 1)
  in
  (* Wrap the term in a span which holds the path to the term. *)
  (* TODO : format the path correctly. *)
  let path_str = String.concat "," @@ List.map string_of_int path in
  span ~attribs:[ Xml.string_attrib "id" path_str ] content

(***************************************************************************************)
(** Backend-specific code. *)

let term_to_string ?(width = 40) env t : string =
  assert (0 <= width);
  PpString.pp ~width (pp_term env [] t)

let term_to_xml ?(width = 40) env t : Xml.elt =
  assert (0 <= width);
  let xml = PpXml.pp ~width (pp_term env [] t) in
  match xml with
  | [ element ] -> element
  | _ ->
      failwith
      @@ Format.sprintf
           "Notation.term_to_xml : expected a single Xml element (got %d)"
           (List.length xml)
