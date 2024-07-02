open Utils.Pervasive
open Lang
open Logic
open Tyxml
module Pp = Utils.Pp

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

(** Pretty-print a global variable using its symbol. *)
let pp_global env name =
  let info = Name.Map.find name env.Env.pp_info in
  (* Take care that the symbol can use utf-8 characters. *)
  Pp.utf8string info.symbol

(** Pretty-print a binder. *)
let pp_binder env (binder : Term.binder) =
  match binder with
  | Anonymous -> Pp.char '_'
  | Named name -> Pp.utf8string @@ Name.show name

(** [is_nat_constant t] checks if [t] is a natural number of the form [S (S (... O))]. *)
let rec is_nat_constant (t : Term.t) : bool =
  match t with
  | Cst c when c = Constants.zero -> true
  | App (_, f, [ arg ]) when f = Term.mkCst Constants.succ ->
      is_nat_constant arg
  | _ -> false

(** [get_nat_constant t] gets [t] the natural number corresponding to [t]. *)
let rec get_nat_constant (t : Term.t) : int =
  match t with
  | Cst c when c = Constants.zero -> 0
  | App (_, f, [ arg ]) when f = Term.mkCst Constants.succ ->
      get_nat_constant arg + 1
  | _ -> assert false

let is_dep_prod (term : Term.t) : bool =
  match term with
  | Term.Prod (_, x, ty, body) when Term.contains_loose_bvars body -> true
  | _ -> false

let is_exist = function
  | Term.App (_, Cst ex, [ _; Lambda _ ]) when Name.equal ex Constants.ex ->
      true
  | _ -> false

let extend i (path : Path.t) : Path.t = { path with sub = i :: path.sub }
let reverse (path : Path.t) : Path.t = { path with sub = List.rev path.sub }

(** Get the precedence level associated to a term. *)
let get_precedence (env : Env.t) (term : Term.t) : Precedence.t =
  match term with
  (* Atoms : these never need parentheses. *)
  | Cst _ | Sort _ | FVar _ | BVar _ -> NeverParen
  | n when is_nat_constant n -> NeverParen
  (* Non-dependent product. *)
  | Prod (_, _, _, body) when not @@ Term.contains_loose_bvars body -> Level 99
  (* Dependent product. *)
  | Prod _ -> Level 100
  (* Existential quantifier. *)
  | App (_, Cst ex, [ _; Lambda _ ]) when Name.equal ex Constants.ex ->
      Level 100
  (* Lambda abstraction. *)
  | Lambda _ -> Level 100
  (* For an applied constant we get the precedence in the environment. *)
  | App (_, Cst name, args) ->
      let info = Name.Map.find name env.pp_info in
      info.precedence
  (* Default application. *)
  | App _ -> Level 0

(** [arrange_app env f args] arranges the function and arguments of the 
    application [App (_, f, args)] in the correct order, accounting for infix/suffix
    functions. We retain for each argument its original position in the list [f :: args].
    
    As usual this assumes [args] is nonempty and [f] is not itself an application. *)
let arrange_app env f args : (int * Term.t) list =
  assert (args != []);
  match (f : Term.t) with
  | Cst name ->
      let info = Name.Map.find name env.Env.pp_info in
      let args = Env.filter_args info (indices ~start:1 args) in
      begin
        match (info.position, args) with
        | Prefix, args -> (0, f) :: args
        | Suffix, [ arg ] -> [ arg; (0, f) ]
        | Infix, [ arg1; arg2 ] -> [ arg1; (0, f); arg2 ]
        | Infix, [ arg ] -> [ arg; (0, f) ]
        | _ ->
            failwith
              "Notation.arrange_app : unexpected position/argument combination"
      end
  | _ -> indices (f :: args)

(** [pp_term prec env path ctx t] pretty-prints the term [t]. 
    - [ctx] keeps track of the names of the free variables (FVars) 
      encountered so far. 
    - [path] keeps track of the path to the term [t], 
      and is used to annotate the Xml divs of each subterm. 
    - [max_prec] is the maximum allowed precedence level : 
      if the precedence of [t] is greater than [max_prec] 
      we surround [t] with parentheses.
*)
let rec pp_term max_prec env (path : Path.t) ctx (t : Term.t) : annot Pp.doc =
  let open Pp in
  (* Compute the current precedence level. *)
  let prec = get_precedence env t in
  (* Pretty-print [t] without the outer-most parentheses. *)
  let content =
    match t with
    (* Atoms. *)
    | BVar _ -> failwith "Notation.pp_term : loose bvar"
    (* We have to print natural numbers e.g. [S (S (O))] in a special way. *)
    | _ when is_nat_constant t ->
        (* Traversing [t] twice is not ideal but oh well... *)
        let n = get_nat_constant t in
        string @@ string_of_int n
    | FVar fvar ->
        let entry = Option.get @@ Context.find fvar ctx in
        pp_binder env entry.binder
    | Cst name -> pp_global env name
    | Sort `Prop -> string "Prop"
    | Sort `Type -> string "Type"
    (* Lambda. *)
    | Lambda (_, x, ty, body) ->
        let fvar, new_ctx = Context.add_fresh x ty ctx in
        let pp_binder = string "λ" ^+^ pp_binder env x ^+^ string ":" in
        let pp_ty =
          pp_term max_prec env (extend 0 path) ctx ty ^+^ utf8string "⇒"
        in
        let pp_body =
          pp_term Precedence.(Level max_level) env (extend 1 path) new_ctx
          @@ Term.instantiate fvar body
        in
        (pp_binder ^//^ pp_ty) ^//^ pp_body
    (* Non-dependent product. *)
    | Prod (_, _, t1, t2) when not (Term.contains_loose_bvars t2) ->
        let pp_t1 =
          pp_term Precedence.(Level max_level) env (extend 0 path) ctx t1
        in
        let pp_t2 =
          pp_term Precedence.(Level max_level) env (extend 1 path) ctx t2
        in
        (* Combine the results. *)
        (pp_t1 ^+^ utf8string "➞") ^//^ pp_t2
    (* Dependent product. *)
    | Prod (_, x, ty, body) ->
        let fvar, new_ctx = Context.add_fresh x ty ctx in
        let pp_binder = utf8string "∀" ^+^ pp_binder env x ^+^ string ":" in
        let pp_ty =
          pp_term Precedence.(Level max_level) env (extend 0 path) ctx ty
          ^^ string ","
        in
        let pp_body =
          pp_term Precedence.(Level max_level) env (extend 1 path) new_ctx
          @@ Term.instantiate fvar body
        in
        (pp_binder ^//^ pp_ty) ^//^ pp_body
    (* Existential quantifier. *)
    | App (_, Cst ex, [ _; Lambda (_, x, ty, body) ])
      when Name.equal ex Constants.ex ->
        let fvar, new_ctx = Context.add_fresh x ty ctx in
        let pp_binder = utf8string "∃" ^+^ pp_binder env x ^+^ string ":" in
        let pp_ty =
          pp_term
            Precedence.(Level max_level)
            env
            (extend 0 @@ extend 2 path)
            ctx ty
          ^^ string ","
        in
        let pp_body =
          pp_term
            Precedence.(Level max_level)
            env
            (extend 1 @@ extend 2 path)
            new_ctx
          @@ Term.instantiate fvar body
        in
        (pp_binder ^//^ pp_ty) ^//^ pp_body
    | App (_, f, args) ->
        (* Applications are a bit tricky : we have to check if the function is a constant,
           and if so take into account the formatting information about that constant.

           When tracking paths we also take care that the order in which the function
           and arguments are printed is not always the same. *)
        arrange_app env f args
        |> List.map
             begin
               fun (i, t) ->
                 (* The arguments are printed at one level below the level of the constant.  *)
                 pp_term (Precedence.decrease prec) env (extend i path) ctx t
             end
        |> flow (ifflat space (nest 2 hardline))
  in
  (* Add outer parentheses if needed. *)
  let content =
    if Precedence.compare prec max_prec > 0
    then char '(' ^^ content ^^ char ')'
    else content
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
  PpString.pp ~width (pp_term Precedence.(Level max_level) env dummy_path ctx t)

let term_to_xml ?(width = default_width) ?(ctx = Context.empty) path env t :
    Xml.elt =
  assert (0 <= width);
  let xml =
    PpXml.pp ~width (pp_term Precedence.(Level max_level) env path ctx t)
  in
  match xml with
  | [ element ] -> element
  | _ ->
      failwith
      @@ Format.sprintf
           "Notation.term_to_xml : expected a single Xml element (got %d)"
           (List.length xml)

(** For some reason the frontend requires us to :
    - wrap every string (pcdata) in a span.
    - wrap the whole term in a span.
    The frontend being in a horrible state, we comply
    and don't touch to the javascript code. *)
let tidy_xml xml : Xml.elt =
  let span ?(a = []) elt = Xml.node ~a "span" [ elt ] in
  let rec add_spans elt =
    match Xml.content elt with
    | Empty -> Xml.empty ()
    | Comment str -> Xml.comment str
    | EncodedPCDATA str -> span @@ Xml.encodedpcdata str
    | PCDATA str -> span @@ Xml.pcdata str
    | Entity str -> span @@ Xml.entity str
    | Leaf (tag, attribs) -> Xml.leaf tag ~a:attribs
    | Node (tag, attribs, elts) ->
        Xml.node tag ~a:attribs (List.map add_spans elts)
  in
  span @@ add_spans xml
