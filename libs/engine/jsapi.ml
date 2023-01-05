(* -------------------------------------------------------------------- *)
open Utils
open Proof

(* -------------------------------------------------------------------- *)
type source = Handle.t * [`C | `H of Handle.t]

(* -------------------------------------------------------------------- *)
exception InvalidASource
exception InvalidLemmaDB

(* -------------------------------------------------------------------- *)
module Exn : sig
  val register  : (exn -> string option) -> unit
  val translate : exn -> string option
end = struct
  type tx_t = exn -> string option

  let translators = ref ([] : tx_t list)

  let register (tx : tx_t) : unit =
    translators := !translators @ [tx]

  let translate (e : exn) =
    let module E = struct exception Found of string end in

    try
      List.iter
        (fun tx -> tx e |> Option.may (fun msg -> raise (E.Found msg)))
        !translators;
      None

    with E.Found msg -> Some msg
end

(* -------------------------------------------------------------------- *)
module Js : sig
  include module type of Js_of_ocaml.Js

  val as_string : exn -> 'a t -> string
end = struct
  include Js_of_ocaml.Js

  let as_string exn (v : 'a t) =
    let v = Unsafe.coerce v in 
    match to_string (typeof v) with
    | "string" -> to_string v
    | _ -> raise exn
end

(* -------------------------------------------------------------------- *)
let () = Exn.register (fun exn ->
    match exn with
    | Syntax.ParseError _ ->
        Some "invalid goal (parse error)"
    | Fo.DuplicatedEntry (_, name) ->
        Some ("duplicated entry \"" ^ name ^ "\" in goal")
    | Fo.TypingError
    | Fo.RecheckFailure ->
        Some "invalid goal (type error)"
    | TacticNotApplicable ->
        Some "tactic not applicable"
    | LemmaDB.LemmaNotFound name ->
        Some ("lemma \"" ^ name ^ "\" does not exist")
    | _ ->
        None
  )

(* -------------------------------------------------------------------- *)
let (!!) f = fun x ->
  try f x with e ->
    let msg =
      Option.default_delayed
        (fun () ->
          Format.sprintf "internal error: %s" (Printexc.to_string e))
        (Exn.translate e)
    in Js.raise_js_error (new%js Js.error_constr (Js.string msg))

module Path : sig
  val of_obj : 'a Js.t -> CoreLogic.ipath
  val of_array : 'a Js.t Js.js_array Js.t -> CoreLogic.ipath list
  val of_opt : 'a Js.t Js.opt -> CoreLogic.ipath option
end = struct
  let of_obj obj = obj |> Js.as_string InvalidASource |> CoreLogic.ipath_of_path
  let of_array obj = obj |> Js.to_array |> Array.to_list |> List.map of_obj
  let of_opt obj = obj |> Js.Opt.to_option |> Option.map of_obj
end
  
(* -------------------------------------------------------------------- *)
let rec js_proof_engine (proof : Proof.proof) = object%js (_self)
  val proof  = proof
  val handle = Handle.fresh ()

  (* Return a [js_subgoal] array of all the opened subgoals *)
  method subgoals =
    let subgoals = Proof.opened proof in
    let subgoals = List.map (js_subgoal _self) subgoals in
    Js.array (Array.of_list subgoals)

  (* Return true when there are no opened subgoals left *)
  method closed =
    Js.bool (Proof.closed proof)

  (* Return the given action as a binary, base64-encoded string *)
  method getactionb action =
    action |>
    CoreLogic.Translate.export_action (Proof.hidmap _self##.proof) _self##.proof |>
    fun pr -> js_log (pr |> Api.Utils.string_of_action); pr |>
    Api.Logic_b.string_of_action |>
    Base64.encode_string |>
    Js.string

  (* Get the meta-data attached to this proof engine *)
  method getmeta =
    Js.Opt.option (Proof.get_meta proof _self##.handle)

  (* Attach meta-data to the proof engine *)
  method setmeta meta =
    Proof.set_meta proof _self##.handle (Js.Opt.to_option meta)

  (* Get all the proof actions that can be applied to the
   * goal targetted by [asource] as an array of actions.
   *
   * The source is described as a record with the following
   * properties:
   *
   *  - kind (string): the type of the source.
   *    Can be "click", "ctxt" or "dnd".
   *
   *  - path (string) [only for the kind "click"]
   *    ID of the "clicked" item
   *
   *  - source (string) [only for the kind "dnd"]
   *    ID of the item that is being dropped
   *
   *  - destination (string option) [only for the kind "dnd"]
   *    ID of the subterm that received the dropped item
   *
   *  - selection (string list) [all actions]
   *    List of IDs of selected subterms
   *
   * An output action is an object with the following properties:
   *
   *  - description : the textual description of the action
   *  - icon        : optional id of a FontAwesome icon to be used in the description
   *  - ui          : the UI action
   *  - highlight   : a JS array of IDs to highlight
   *  - action      : the related action (see [apply])
   *)
  method actions asource =
    let actions =
      let kinds =
        match Js.to_string (Js.typeof asource) with
        | "string" ->
          [`Click (Path.of_obj asource)]
        | "object" -> begin
          let asource = Js.Unsafe.coerce asource in
          match Js.as_string InvalidASource asource##.kind with
            | "click" ->
                let path = Path.of_obj asource##.path in
                [`Click path]
            | "ctxt" ->
                [`Ctxt]
            | "dnd" ->
                let source = Path.of_obj asource##.source in
                let destination = Path.of_opt asource##.destination in
                [`DnD CoreLogic.{ source; destination; }]
            | "any" ->
                let path = Path.of_obj asource##.path in
                [`Click path; `DnD CoreLogic.{ source = path; destination = None; }]
            | _ -> raise InvalidASource
          end
        | _ -> raise InvalidASource

      and selection = Path.of_array asource##.selection in

      let asource =
        List.map (fun kind -> CoreLogic.{ kind; selection; }) kinds in

      List.flatten (List.map (!!(CoreLogic.actions _self##.proof)) asource)
    in

    Js.array (
      Array.of_list
        (List.map (fun CoreLogic.{ description = p; icon = ic;
                                   highlights = ps; kind = aui; action = a } -> 
           let ps = List.map CoreLogic.path_of_ipath ps in
           let ps = Js.array (Array.of_list (List.map Js.string ps)) in

           let aui =
             let p2p = CoreLogic.path_of_ipath in

             match aui with
             | `Click p -> Js.Unsafe.obj [|
                 "kind"  , Js.Unsafe.inject (Js.string "click");
                 "target", Js.Unsafe.inject (Js.string (p2p p));
               |]

             | `DnD (src, dst) -> Js.Unsafe.obj [|
                 "kind"       , Js.Unsafe.inject (Js.string "dnd");
                 "source"     , Js.Unsafe.inject (Js.string (p2p src));
                 "destination", Js.Unsafe.inject (Js.string (p2p dst));
               |]

             | `Ctxt -> Js.Unsafe.obj [|
                 "kind"       , Js.Unsafe.inject (Js.string "ctxt");
               |]
           in

           let icon =
             match ic with
             | Some s -> Js.Unsafe.inject (Js.string s)
             | None -> Js.Unsafe.inject Js.undefined in

           Js.Unsafe.obj [|
             "description", Js.Unsafe.inject (Js.string p) ;
             "icon"       , icon                           ;
             "highlight"  , Js.Unsafe.inject ps            ;
             "ui"         , aui                            ;
             "action"     , Js.Unsafe.inject a             |]) actions))

  (* Same as [actions], but in async mode. TO BE TESTED *)
  method pactions path =
    let%lwt _ = Lwt.return () in Lwt.return (_self##actions path)

  (* Apply the action [action] (as returned by [actions]) *)
  method apply action =
    js_proof_engine (!! (curry CoreLogic.apply) (_self##.proof, action))
  
  (* Load the lemma database specified by the [lemmas] object into the prover *)
  method loaddb lemmas =
    let lemmas : (string * string) list =
      match Js.to_string (Js.typeof lemmas) with
      | "object" ->
          lemmas |> Js.object_keys |> Js.to_array |> Array.to_list |>
          List.map begin fun name ->
            let name = Js.as_string InvalidLemmaDB name in
            let stmt = Js.as_string InvalidLemmaDB (Js.Unsafe.get lemmas name) in
            (name, stmt)
          end
      | _ -> raise InvalidLemmaDB
      in
    let pr = Proof.loaddb _self##.proof lemmas in
    js_proof_engine pr

  (* Serialize the current lemma database into a JS object. If [selection] is
     defined, filters out lemmas which cannot be applied to the selection. *)
  method getdb selection =
    let selection = selection |> Js.Optdef.to_option |> Option.map Path.of_array in
    _self##.proof |> CoreLogic.lemmas ?selection |>
    List.map begin fun (name, form) ->
      let stmt =
        Fo.Notation.f_tostring (LemmaDB.env (Proof.db _self##.proof)) form |>
        Js.string |>
        Js.Unsafe.inject
      in name, stmt
    end |>
    Array.of_list |>
    Js.Unsafe.obj
end

(* -------------------------------------------------------------------- *)
(* JS wrapper for subgoals                                              *)
and js_subgoal parent (handle : Handle.t) = object%js (_self)
  (* back-link to the [js_proof_engine] this subgoal belongs to *)
  val parent = parent

  (* the handle (UID) of the subgoal *)
  val handle = handle

  (* the OCaml subgoal *)
  method goal =
    Proof.byid parent##.proof _self##.handle

  (* Return all the functional variables as a [string array] *)
  method fvars =
    let goal = _self##goal in
    let fvars : string list =
      Fo.Funs.all goal.g_env |>
      Map.bindings |>
      List.map (fun (f, (ar, res)) ->
        let ar = List.to_string ~sep:" & " ~left:"" ~right:"" (Fo.Notation.t_tostring goal.Proof.g_env) ar in
        let res = Fo.Notation.t_tostring goal.g_env res in
        Printf.sprintf "%s : %s -> %s" f ar res) in
    Js.array (Array.of_list (List.map Js.string fvars))

  (* Return all the propositional variables as a [string array] *)
  method pvars =
    let goal = _self##goal in
    let pvars = List.fst (Map.bindings (Fo.Prps.all goal.g_env)) in
    Js.array (Array.of_list (List.map Js.string pvars))

  (* Return all the local variables as a [js_tvar array] *)
  method tvars =
    let goal  = _self##goal in
    let tvars = Fo.Vars.to_list goal.g_env in
    let aout  = List.mapi (fun i (id, x, b) ->
      js_tvar _self (i, (Handle.ofint id, x, b))) tvars in
    Js.array (Array.of_list aout)

  (* Return all the local hypotheses (context) as a [js_hyps array] *)
  method context =
    let goal = _self##goal in
    let hyps = List.rev (Proof.Hyps.to_list goal.g_hyps) in

    Js.array (Array.of_list (List.mapi (fun i x -> js_hyps _self (i, x)) hyps))

  (* Return the subgoal conclusion as a [js_form] *)
  method conclusion =
    let goal  = Proof.byid parent##.proof _self##.handle in
    js_form _self (_self##.handle, `C) goal.g_goal

  (* [this#intro [variant : int]] applies the relevant introduction
   * rule to the conclusion of the subgoal [this]. The parameter
   * [variant] gives the variant of the introduction rule to be applied.
   *
   * See [#ivariants] *)

  method intro variant =
    js_proof_engine (!!(CoreLogic.intro ~variant) (parent##.proof, handle))

  (* [this#elim (target : handle<js_hyps>)]] applies the relevant elimination
   * rule to the hypothesis [target] of the subgoal [this].
   *
   * Raise an exception if [target] does not belong to [this] *)
  method elim target =
    let data = (target, (parent##.proof, handle)) in
    js_proof_engine (!!(curry CoreLogic.elim) data)

  (* [this#ivariants] Return the available introduction rules that can
   * be applied to the conclusion of [this] as a string array. The strings
   * are only for documentation purposes - only their position in the
   * returned array is meaningful and can be used as argument to [#intro]
   * to select the desired introduction rule. *)
  method ivariants =
    let aout = !!CoreLogic.ivariants (parent##.proof, handle) in
    let aout = Array.of_list (List.map Js.string aout) in
    Js.array aout

  (* [this#cut (form : string)] parses [form] in the goal [context] and
   * cut it. *)
  method cut form =
    let doit () =
      let goal = _self##goal in
      let form = String.trim (Js.to_string form) in
      let form = Io.parse_form (Io.from_string form) in
      let form = Fo.Form.check goal.g_env form in
      CoreLogic.cut form (parent##.proof, _self##.handle)
    in js_proof_engine (!!doit ())
  
  (* [this#getcutb (form : string)] parses [form] in the current goal, and
   * returns the base64-encoded string of the corresponding ACut action. *)
  method getcutb form =
      let goal = _self##goal in
      let form = form |>
        Js.to_string |> String.trim |>
        Io.from_string |> Io.parse_form |>
        Fo.Form.check goal.g_env |>
        Fo.Translate.of_form in
    `ACut form |>
    Api.Logic_b.string_of_action |>
    Base64.encode_string |>
    Js.string
    
  
  (* [this#addlemma (name : string)] retrieves the lemma [name] in the database,
     and adds it as a new hypothesis in the current goal. *)
  method addlemma name =
    let doit () =
      let name = Js.to_string name in
      let form = LemmaDB.find (Proof.db parent##.proof) name in
      CoreLogic.assume form (parent##.proof, _self##.handle)
    in js_proof_engine (!!doit ())
      

  (* [this#add_local (name : string) (expr : string) parses [expr] in the goal
   * [context] and adds it to the local [context] under the name [name]. *)
  method addlocal name expr =
    let doit () =
      let goal = _self##goal in
      let expr = String.trim (Js.to_string expr) in
      let expr = Io.parse_expr (Io.from_string expr) in
      let expr, ty = Fo.Form.echeck goal.g_env expr in
      CoreLogic.add_local_def (Js.to_string name, ty, expr) (parent##.proof, _self##.handle)

    in js_proof_engine (!!doit ())

  (* [this#add_alias (nexpr : string) parses [nexpr] as a named expression
   * in the goal [context] and add it to the local [context]. *)
  method addalias expr =
    let doit () =
      let goal = _self##goal in
      let expr = String.trim (Js.to_string expr) in
      let name, expr = Io.parse_nexpr (Io.from_string expr) in
      let expr, ty = Fo.Form.echeck goal.g_env expr in
      CoreLogic.add_local_def (Location.unloc name, ty, expr) (parent##.proof, _self##.handle)

    in js_proof_engine (!!doit ())

  (* [this#getaliasb (nexpr : string) parses [nexpr] as a named expression
   * in the current goal, and returns the base64-encoded string of the
   * corresponding ADef action. *)
  method getaliasb expr =
    let goal = _self##goal in
    let expr = String.trim (Js.to_string expr) in
    let name, expr = Io.parse_nexpr (Io.from_string expr) in
    let expr, ty = Fo.Form.echeck goal.g_env expr in
    let name = Location.unloc name in
    let expr, ty = Fo.Translate.(of_expr expr, of_type_ ty) in
    `ADef (name, ty, expr) |>
    Api.Logic_b.string_of_action |>
    Base64.encode_string |>
    Js.string

  (* [this#move_hyp (from : handle<js_hyp>) (before : handle<js_hyp> option)] move
   * hypothesis [from] before hypothesis [before]. Both hypothesis
   * must be part of this sub-goal. *)
  method movehyp from before =
    let doit () =
      CoreLogic.move
        from (Js.Opt.to_option before)
        (parent##.proof, _self##.handle)
    in js_proof_engine (!!doit ())

  (* [this#generalize (h : handle<js_hyps>) generalizes the hypothesis [h] *)
  method generalize hid =
    let doit () =
      CoreLogic.generalize hid (parent##.proof, _self##.handle)
    in js_proof_engine (!!doit ())

  method getmeta =
    Js.Opt.option (Proof.get_meta parent##.proof _self##.handle)

  method setmeta meta =
    Proof.set_meta parent##.proof _self##.handle (Js.Opt.to_option meta)
  
  method toascii =
    let funs : string list =
      _self##fvars |> Js.to_array |> Array.to_list |> List.map Js.to_string in
    let props : string list =
      _self##pvars |> Js.to_array |> Array.to_list |> List.map Js.to_string in
    let vars : string list =
      _self##tvars |> Js.to_array |> Array.to_list |> List.map (fun v -> v##toascii |> Js.to_string) in
    let hyps : string list =
      _self##context |> Js.to_array |> Array.to_list |> List.map (fun h -> h##toascii |> Js.to_string) in
    let concl : string =
      _self##conclusion |> fun c -> c##toascii |> Js.to_string in
    
    let to_string = List.to_string ~sep:", " ~left:"" ~right:"" identity in
    let comma =
      "" |> List.fold_left (fun s l ->
        if String.is_empty s then
          if List.is_empty l then ""
          else to_string l
        else
          if List.is_empty l then s
          else s ^ ", " ^ to_string l) in

    Js.string (Printf.sprintf "%s; %s |- %s"
      (comma [funs; vars; props])
      (to_string hyps)
      concl)

  method tostring =
    let hyps : string list =
      _self##context |> Js.to_array |> Array.to_list |> List.map (fun h -> h##tostring |> Js.to_string) in
    let concl : string =
      _self##conclusion |> fun c -> c##tostring |> Js.to_string in
    
    let to_string = List.to_string ~sep:", " ~left:"" ~right:"" identity in

    Js.string (Printf.sprintf "%s ⊢ %s"
      (to_string hyps)
      concl)
end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for a context hypothesis                                  *)
and js_hyps parent (i, (handle, hyp) : int * (Handle.t * Proof.hyp)) =
object%js (_self)
  (* back-link to the [js_subgoal] this hypothesis belongs to *)
  val parent = parent

  (* the handle (UID) of the hypothesis *)
  val handle = handle

  (* the handle (UID) of the parent hypothesis *)
  val phandle = Js.Opt.option hyp.h_src

  (* the handle position in its context *)
  val position = i

  (* if the hypothesis is fresh / new *)
  val fresh = Js.bool (hyp.h_gen <= 1)

  (* the hypothesis as a [js_form] *)
  val form = js_form parent (parent##.handle, `H handle) hyp.h_form

  (* The enclosing proof engine *)
  val proof = parent##.parent

  (* Return the [html] of the enclosed formula *)  
  method html =
    _self##.form##html

  (* Return the [mathml] of the enclosed formula *)  
  method mathml =
    _self##.form##mathml

  (* Return an UTF8 string representation of the enclosed formula *)
  method tostring =
    _self##.form##tostring

  (* Return an ASCII string representation of the enclosed formula *)
  method toascii =
    _self##.form##toascii

  method getmeta =
    Js.Opt.option (Proof.get_meta _self##.proof##.proof _self##.handle)

  method setmeta meta =
    Proof.set_meta _self##.proof##.proof _self##.handle (Js.Opt.to_option meta)
end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for a local variable                                      *)
and js_tvar parent ((i, (handle, x, (ty, b))) : int * (Handle.t * Fo.vname * Fo.bvar)) =
object%js (_self)
  (* back-link to the [js_subgoal] this local variable belongs to *)
  val parent = parent

  (* the handle of the local variable *)
  val handle = handle

  (* the handle position in its context *)
  val position = i

  (* the local variable name, as an OCaml string *)
  val oname = Fo.Notation.e_tostring (parent##goal).g_env (EVar x)

  (* the local variable name *)
  method name = Js.string _self##.oname

  (* the local variable type as a [js_type] *)
  val type_ = js_type parent ty

  (* the local definition - return an optional expression *)
  val body =
    Js.Opt.option (Option.map (js_expr parent) b)

  (* the enclosing proof engine *)
  val proof = parent##.parent

  method prefix (b : bool) =
    Format.sprintf "%d/V%s#%d%s"
      (Handle.toint _self##.parent##.handle)
      (if b then "b" else "h")
      (Handle.toint _self##.handle)
      (if b then "" else ":")
  
  (* the path to the local variable's head *)
  method idhead = _self##prefix false

  (* the path to the local variable's body *)
  method idbody = _self##prefix true

  (* Return the [html] of the enclosed local variable *)  
  method html =
    let open Tyxml in
    let open Utils.Html in

    let dt =
      span [
        span begin
          [span ~a:[Xml.string_attrib "id" _self##idhead] begin
            [span
              [Xml.pcdata (UTF8.of_latin1 _self##.oname)]] @
              spaced [span [Xml.pcdata ":"]] @
              [Fo.Notation.t_tohtml (parent##goal).g_env ty]
          end]
          @
          match b with
          | Some b ->
              spaced [span [Xml.pcdata ":="]] @
              [Fo.Notation.e_tohtml ~id:(Some _self##idbody) (parent##goal).g_env b]
          | None -> []
        end]
    in Js.string (Format.asprintf "%a" (Tyxml.Xml.pp ()) dt)

  (* Return the [mathml] of the enclosed local variable *)  
  method mathml =
    let open Tyxml in
    let open Utils.Mathml in

    let dt =
      math [
        row begin
          [row ~a:[Xml.string_attrib "id" _self##idhead] begin
            [mi (UTF8.of_latin1 (Fo.Notation.e_tostring (parent##goal).g_env (EVar x)))] @
            [mo ":"] @
            [Fo.Notation.t_tomathml (parent##goal).g_env ty]
          end]
          @
          match b with
          | Some b ->
              [mo ":="] @
              [Fo.Notation.e_tomathml ~id:(Some _self##idbody) (parent##goal).g_env b]
          | None -> []
        end]
    in Js.string (Format.asprintf "%a" (Tyxml.Xml.pp ()) dt)

  (* Return an UTF8 string representation of the enclosed local variable *)
  method tostring =
    match b with
    | Some b ->
        Js.string (Format.sprintf "%s : %s := %s"
          (Fo.Notation.e_tostring (parent##goal).g_env (EVar x))
          (Fo.Notation.t_tostring (parent##goal).g_env ty)
          (Fo.Notation.e_tostring (parent##goal).g_env b))
    | None ->
        Js.string (Format.sprintf "%s : %s"
          (Fo.Notation.e_tostring (parent##goal).g_env (EVar x))
          (Fo.Notation.t_tostring (parent##goal).g_env ty))

  (* Return an ASCII string representation of the enclosed local variable *)
  method toascii =
    match b with
    | Some b ->
        Js.string (Format.sprintf "%s := %s"
          (Fo.Notation.e_tostring (parent##goal).g_env (EVar x))
          (Fo.Notation.e_toascii (parent##goal).g_env b))
    | None ->
        Js.string (Format.sprintf "%s : %s"
          (Fo.Notation.e_tostring (parent##goal).g_env (EVar x))
          (Fo.Notation.t_toascii (parent##goal).g_env ty))

  method getmeta =
    Js.Opt.option (Proof.get_meta _self##.proof##.proof _self##.handle)

  method setmeta meta =
    Proof.set_meta _self##.proof##.proof _self##.handle (Js.Opt.to_option meta)
end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for formulas                                              *)
and js_form parent (source : source) (form : Fo.form) = object%js (_self)
  (* The prefix for all subpaths of the formula *)
  val prefix =
    match source with
    | h, `H i -> Format.sprintf "%d/H#%d" (Handle.toint h) (Handle.toint i)
    | h, `C   -> Format.sprintf "%d/C#0" (Handle.toint h)
  
  (* Return the [mathml] of the formula *)  
  method mathml =
    _self##mathmltag true

  (* Return the [html] of the formula *)  
  method html =
    _self##htmltag true

  (* Return the [mathml] of the formula *)  
  method mathmltag (id : bool) =
    let prefix =
      if not id then None else Some _self##.prefix in
    Js.string
      (Format.asprintf "%a" (Tyxml.Xml.pp ())
      (Utils.Mathml.math [Fo.Notation.f_tomathml (parent##goal).g_env ~id:prefix form]))

  (* Return the [html] of the formula *)  
  method htmltag (id : bool) =
    let prefix =
      if not id then None else Some _self##.prefix in
    Js.string
      (Format.asprintf "%a" (Tyxml.Xml.pp ())
      (Fo.Notation.f_tohtml (parent##goal).g_env ~id:prefix form))

  (* Return an UTF8 string representation of the formula *)
  method tostring =
    Js.string (Fo.Notation.f_tostring (parent##goal).g_env form)

  (* Return an ASCII string representation of the formula *)
  method toascii =
    Js.string (Fo.Notation.f_toascii (parent##goal).g_env form)
end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for expressions                                           *)
and js_expr parent (expr : Fo.expr) = object%js (_self)
  (* Return the [mathml] of the formula *)  
  method mathml =
    _self##mathmltag

  (* Return the [html] of the formula *)  
  method html =
    _self##htmltag

  (* Return the [mathml] of the formula *)  
  method mathmltag =
    Js.string
      (Format.asprintf "%a" (Tyxml.Xml.pp ())
      (Utils.Mathml.math [Fo.Notation.e_tomathml (parent##goal).g_env expr]))

  (* Return the [html] of the formula *)  
  method htmltag =
    Js.string
      (Format.asprintf "%a" (Tyxml.Xml.pp ())
      (Fo.Notation.e_tohtml (parent##goal).g_env expr))

  (* Return an UTF8 string representation of the expression *)
  method tostring =
    Js.string (Fo.Notation.e_tostring (parent##goal).g_env expr)
end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for types                                                 *)
and js_type parent (ty : Fo.type_) = object%js (_self)
  (* Return the raw [mathml] of the type *)
  method rawmathml =
    Utils.Mathml.math [Fo.Notation.t_tomathml (parent##goal).g_env ty]

  (* Return the raw [html] of the type *)
  method rawhtml =
    Fo.Notation.t_tohtml (parent##goal).g_env ty

  (* Return the raw string representation of the type *)
  method rawstring =
    Fo.Notation.t_tostring (parent##goal).g_env ty

  (* Return the [mathml] of the type *)  
  method mathml =
    Js.string (Format.asprintf "%a" (Tyxml.Xml.pp ()) _self##rawmathml)

  (* Return the [html] of the type *)  
  method html =
    Js.string (Format.asprintf "%a" (Tyxml.Xml.pp ()) _self##rawhtml)

  (* Return an UTF8 string representation of the formula *)
  method tostring =
    Js.string _self##rawstring
end

(* -------------------------------------------------------------------- *)
let export (name : string) : unit =
  Js.export name (object%js
    (* [this#parse input] parse the goal [input] and return a
     * [js_proof_engine] for it.
     *
     * Raise an exception if [input] is invalid *)
    method parse x =
      let env, hyps, goal = !!(fun () ->
        let goal = String.trim (Js.to_string x) in
        let goal = Io.parse_goal (Io.from_string goal) in
        Fo.Goal.check goal
      ) () in js_proof_engine (Proof.init env hyps goal)

    (* [this#parseToUnicode input] parses the goal [input] and returns
     * its unicode representation.
     *
     * Raise an exception if [input] is invalid *)
    method parseToUnicode x =
      let env, hyps, goal = !!(fun () ->
          let goal = String.trim (Js.to_string x##.input) in
          let goal = Io.parse_goal (Io.from_string goal) in
          Fo.Goal.check goal
        ) () in

      Js.string (Printf.sprintf "%s⊢ %s"
        (Js.Optdef.case x##.printHyps
          (fun _ -> "")
          (fun b -> if not (Js.to_bool b) then ""
                    else List.to_string
                           ~sep:", " ~left:"" ~right:" "
                           (Fo.Notation.f_tostring env) hyps))
        (Fo.Notation.f_tostring env goal))

    (* Return a new proof engine whose goals are the base64, binary decoding of [goalsb]  *)
    method setgoalsb goalsb =
      let goals =
        goalsb |>
        Js.to_string |>
        Base64.decode_exn |>
        Api.Logic_b.goals_of_string in
      let gls, hms = goals |> List.map Proof.Translate.import_goal |> List.split in
      let hm = List.fold_left Hidmap.union Hidmap.empty hms in
      js_proof_engine (Proof.ginit hm gls)
  end)
