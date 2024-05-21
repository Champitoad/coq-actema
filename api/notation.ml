open Lang
open Logic
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

let paren ?(doit = true) x =
  let open Pp in
  if doit then char '(' ^^ x ^^ char ')' else x

(** [filter_args implicits args] filters out the implicit arguments in [args]. *)
let filter_args implicits args =
  let rec loop implicits args kept i =
    match (args, implicits) with
    | arg :: args, imp :: implicits ->
        if i = imp
        then loop implicits args kept (i + 1)
        else loop (imp :: implicits) args (arg :: kept) (i + 1)
    | _, [] ->
        (* All the remaining arguments are explicit. *) List.rev kept @ args
    | [], _ :: _ ->
        (* There are remaining implicits but no more args. *) assert false
  in
  loop (List.sort Int.compare implicits) args [] 0

(** Get the formatting information for a name. *)
let name_info env name =
  match Name.Map.find_opt name env.Env.pp_info with
  | Some info -> info
  | None -> Env.default_pp_info (Name.show name)

(** Pretty-print a global variable using its symbol. *)
let pp_global env name =
  let info = name_info env name in
  Pp.string info.symbol

(** Pretty-print a local variable. *)
let pp_local env name = Pp.string @@ Name.show name

(** Pretty-print a binder. *)
let pp_binder env name = Pp.string @@ Name.show name

(** [is_nat_constant t] checks if [t] is a natural number of the form [S (S (... O))]. *)
let rec is_nat_constant (t : Term.t) : bool =
  match t with
  | Cst c when c = Name.zero -> true
  | App (f, [ arg ]) when f = Term.mkCst Name.succ -> is_nat_constant arg
  | _ -> false

(** [get_nat_constant t] gets [t] the natural number corresponding to [t]. *)
let rec get_nat_constant (t : Term.t) : int =
  match t with
  | Cst c when c = Name.zero -> 0
  | App (f, [ arg ]) when f = Term.mkCst Name.succ -> get_nat_constant arg + 1
  | _ -> assert false

let extend i (path : Path.t) : Path.t = { path with sub = i :: path.sub }
let reverse (path : Path.t) : Path.t = { path with sub = List.rev path.sub }

(** [pp_term env path t] pretty-prints the term [t]. 
    The argument [path] keeps track of the path to the term [t], 
    and is used to annotate the Xml divs of each subterm. *)
let rec pp_term env (path : Path.t) ctx (t : Term.t) : annot Pp.doc =
  let open Pp in
  let content =
    match t with
    (* We have to print natural numbers e.g. [S (S (O))] in a special way. *)
    | _ when is_nat_constant t ->
        (* Traversing [t] twice is not ideal but oh well... *)
        let n = get_nat_constant t in
        string @@ string_of_int n
    | Var v ->
        let name, _ = Option.get @@ Context.get v ctx in
        pp_local env name
    | Cst name -> pp_global env name
    | Sort `Prop -> string "Prop"
    | Sort `Type -> string "Type"
    | Lambda (name, ty, body) ->
        let pp_binder = string "fun" ^+^ pp_binder env name ^+^ string ":" in
        let pp_ty = pp_term env (extend 0 path) ctx ty ^+^ utf8string "⇒" in
        let pp_body =
          pp_term env (extend 1 path) (Context.push name ty ctx) body
        in
        (pp_binder ^//^ pp_ty) ^//^ pp_body
    | Arrow (t1, t2) ->
        (* We might or might not need to add parentheses around [t1]. *)
        let doit =
          match t1 with
          | Var _ | Cst _ | App _ | Sort _ -> false
          | _ when is_nat_constant t1 -> false
          | _ -> true
        in
        let pp_t1 = paren ~doit @@ pp_term env (extend 0 path) ctx t1 in
        (* We don't need parentheses around [t2]. *)
        let pp_t2 = pp_term env (extend 1 path) ctx t2 in
        (* Combine the results. *)
        (pp_t1 ^+^ utf8string "→") ^//^ pp_t2
    | Prod (name, ty, body) ->
        let pp_binder = utf8string "∀" ^+^ pp_binder env name ^+^ string ":" in
        let doit = match ty with Prod _ -> true | _ -> false in
        let pp_ty =
          paren ~doit (pp_term env (extend 0 path) ctx ty) ^^ string ","
        in
        let pp_body =
          pp_term env (extend 1 path) (Context.push name ty ctx) body
        in
        (pp_binder ^//^ pp_ty) ^//^ pp_body
    | App (f, args) ->
        (* Applications are a bit tricky : we have to check if the function is a constant,
           and if so take into account the formatting information about that constant. *)
        let elts =
          match f with
          | Cst name ->
              let info = name_info env name in
              let args = filter_args info.implicit_args args in
              begin
                match (info.position, args) with
                | Prefix, args -> f :: args
                | Infix, [ arg1; arg2 ] -> [ arg1; f; arg2 ]
                | Suffix, [ arg ] -> [ arg; f ]
                | _ -> assert false
              end
          | _ -> f :: args
        in
        (* Pretty-print the applications one by one, adding parentheses where needed. *)
        elts
        |> List.mapi
             begin
               fun i (t : Term.t) ->
                 (* Decide whether we need parentheses around [t]. *)
                 let doit =
                   match t with
                   | Var _ | Cst _ | Sort _ -> false
                   | _ when is_nat_constant t -> false
                   | _ -> true
                 in
                 paren ~doit @@ pp_term env (extend i path) ctx t
             end
        |> flow (ifflat space (nest 2 hardline))
  in
  (* Wrap the term in a span which holds the path to the term. *)
  let path_str = Path.to_string @@ reverse path in
  span ~attribs:[ Xml.string_attrib "id" path_str ] content

(***************************************************************************************)
(** Backend-specific code. *)

let default_width = 50

let term_to_string ?(width = default_width) ?(ctx = Context.empty) env t :
    string =
  assert (0 <= width);
  (* The path doesn't matter when printing to a string. *)
  let dummy_path = Path.make 0 in
  PpString.pp ~width (pp_term env dummy_path ctx t)

let term_to_xml ?(width = default_width) ?(ctx = Context.empty) path env t :
    Xml.elt =
  assert (0 <= width);
  let xml = PpXml.pp ~width (pp_term env path ctx t) in
  match xml with
  | [ element ] -> element
  | _ ->
      failwith
      @@ Format.sprintf
           "Notation.term_to_xml : expected a single Xml element (got %d)"
           (List.length xml)
