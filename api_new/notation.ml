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

let span ?(attribs = []) (x : annot Pp.doc) : annot Pp.doc =
  Pp.annotate ("span", attribs) x

let paren x =
  let open Pp in
  char '(' ^^ x ^^ char ')'

(** Get the formatting information for [name]. *)
let get_info env name =
  match Name.Map.find_opt name env.Env.pp_info with
  | Some info -> info
  | None -> { symbol = Name.str name; position = `Prefix }

(** Pretty-print a name using its symbol. *)
let pp_name env name =
  let info = get_info env name in
  Pp.string info.symbol

let rec pp_term env t =
  (* We always wrap a term in a span. *) span @@ pp_term_raw env t

and pp_term_raw env (t : Term.t) : annot Pp.doc =
  let open Pp in
  match t with
  | Var name | Cst name -> pp_name env name
  | Lambda (name, ty, body) ->
      let pp_binder = string "fun" ^+^ pp_name env name ^+^ string ":" in
      let pp_ty = pp_term env ty ^+^ string "=>" in
      let pp_body = pp_term env body in
      (pp_binder ^//^ pp_ty) ^//^ pp_body
  | Arrow (t1, t2) ->
      (* We might or might not need to add parentheses around [t1]. *)
      let pp_t1 =
        match t1 with
        | Var _ | Cst _ | App _ -> pp_term env t1
        | _ -> paren @@ pp_term env t1
      in
      (* We don't need parentheses around [t2]. *)
      let pp_t2 = pp_term env t2 in
      (* Combine the results. *)
      (pp_t1 ^+^ string "->") ^/^ pp_t2
  | Prod (name, ty, body) ->
      let pp_binder = string "forall" ^+^ pp_name env name ^+^ string ":" in
      let pp_ty = pp_term env ty ^^ string "," in
      let pp_body = pp_term env body in
      (pp_binder ^//^ pp_ty) ^//^ pp_body
  | App (f, args) ->
      (* Applications are a bit tricky : we have to check if the function is a constant,
         and if so take into account the formatting information about that constant. *)
      let elts =
        match f with
        | Cst name ->
            let info = get_info env name in
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
      flow_map (break 1)
        begin
          fun t ->
            match (t : Term.t) with
            | Var _ | Cst _ -> pp_term env t
            | _ -> paren @@ pp_term env t
        end
        elts

(***************************************************************************************)
(** Backend-specific code. *)

let term_to_string ?(width = 40) env t : string =
  assert (0 <= width);
  PpString.pp ~width (pp_term env t)

let term_to_xml ?(width = 40) env t : Xml.elt =
  assert (0 <= width);
  Xml.node "span" @@ PpXml.pp ~width (pp_term env t)
