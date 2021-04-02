(* -------------------------------------------------------------------- *)
open Utils
open Proof

(* -------------------------------------------------------------------- *)
type source = Handle.t * [`C | `H of Handle.t]

(* -------------------------------------------------------------------- *)
exception InvalidASource

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
        Some "invalid formula (parse error)"
    | Fo.DuplicatedEntry _ | Fo.TypingError | Fo.RecheckFailure ->
        Some "invalid formula"
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
   *    Can be "click" or "dnd".
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
   *  - description : the description of the action
   *  - ui          : the UI action
   *  - highlight   : a JS array of IDs to highlight
   *  - action      : the related action (see [apply])
   *)
  method actions asource =
    let actions =
      let path_of obj = CoreLogic.ipath_of_path (Js.as_string InvalidASource obj) in
      let path_list_of obj = obj |> Js.to_array |> Array.to_list |> List.map path_of in
      let path_option_of obj = obj |> Js.Opt.to_option |> Option.map path_of in

      let kinds =
        match Js.to_string (Js.typeof asource) with
        | "string" ->
          [`Click (path_of asource)]
        | "object" -> begin
          let asource = Js.Unsafe.coerce asource in
          match Js.as_string InvalidASource asource##.kind with
            | "click" ->
                let path = path_of asource##.path in
                [`Click path]
            | "dnd" ->
                let source = path_of asource##.source in
                let destination = path_option_of asource##.destination in
                [`DnD CoreLogic.{ source; destination; }]
            | "any" ->
                let path = path_of asource##.path in
                [`Click path; `DnD CoreLogic.{ source = path; destination = None; }]
            | _ -> raise InvalidASource
          end
        | _ -> raise InvalidASource

      and selection = path_list_of asource##.selection in

      let asource =
        List.map (fun kind -> CoreLogic.{ kind; selection; }) kinds in

      List.flatten (List.map (!!(CoreLogic.actions _self##.proof)) asource)
    in

    Js.array (
      Array.of_list
        (List.map (fun (p, ps, aui, a) -> 
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
           in               

           Js.Unsafe.obj [|
             "description", Js.Unsafe.inject (Js.string p) ;
             "highlight"  , Js.Unsafe.inject ps            ;
             "ui"         , aui                            ;
             "action"     , Js.Unsafe.inject a             |]) actions))

  (* Same as [actions], but in async mode. TO BE TESTED *)
  method pactions path =
    let%lwt _ = Lwt.return () in Lwt.return (_self##actions path)

  (* Apply the action [action] (as returned by [actions]) *)
  method apply action =
    js_proof_engine (!! (curry CoreLogic.apply) (_self##.proof, action))
end

(* -------------------------------------------------------------------- *)
(* JS wrapper for subgoals                                              *)
and js_subgoal parent (handle : Handle.t) = object%js (_self)
  (* back-link to the [js_proof_engine] this subgoal belongs to *)
  val parent = parent

  (* the handle (UID) of the subgoal *)
  val handle = handle

  (* Return all the propositional variables as a [string array] *)
  method vars =
    let goal = Proof.byid parent##.proof _self##.handle in
    let vars = List.fst (Map.bindings (Fo.Prps.all goal.g_env)) in
    Js.array (Array.of_list (List.map Js.string vars))

  (* Return all the local variables as a [js_tvar array] *)
  method tvars =
    let goal  = Proof.byid parent##.proof _self##.handle in
    let tvars = Fo.Vars.to_list goal.g_env in
    let aout  = List.mapi (fun i (id, x, b) ->
      js_tvar _self (i, (Handle.ofint id, x, b))) tvars in
    Js.array (Array.of_list aout)

  (* Return all the local hypotheses (context) as a [js_hyps array] *)
  method context =
    let goal = Proof.byid parent##.proof _self##.handle in
    let hyps = List.rev (Proof.Hyps.to_list goal.g_hyps) in

    Js.array (Array.of_list (List.mapi (fun i x -> js_hyps _self (i, x)) hyps))

  (* Return the subgoal conclusion as a [js_form] *)
  method conclusion =
    let goal  = Proof.byid parent##.proof _self##.handle in
    js_form (_self##.handle, `C) goal.g_goal

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
      let goal = Proof.byid parent##.proof _self##.handle in
      let form = String.trim (Js.to_string form) in
      let form = Io.parse_form (Io.from_string form) in
      let form = Fo.Form.check goal.g_env form in
      CoreLogic.cut form (parent##.proof, _self##.handle)
    in js_proof_engine (!!doit ())

  (* [this#add_local (name : string) (expr : string) parses [expr] in the goal
   * [context] and adds it to the local [context] under the name [name]. *)
  method addlocal name expr =
    let doit () =
      let goal = Proof.byid parent##.proof _self##.handle in
      let expr = String.trim (Js.to_string expr) in
      let expr = Io.parse_expr (Io.from_string expr) in
      let expr, ty = Fo.Form.echeck goal.g_env expr in
      CoreLogic.add_local (Js.to_string name, ty, Some expr) (parent##.proof, _self##.handle)

    in js_proof_engine (!!doit ())

  (* [this#add_alias (nexpr : string) parses [nexpr] as a named expression
   * in the goal [context] and add it to the local [context]. *)
  method addalias expr =
    let doit () =
      let goal = Proof.byid parent##.proof _self##.handle in
      let expr = String.trim (Js.to_string expr) in
      let name, expr = Io.parse_nexpr (Io.from_string expr) in
      let expr, ty = Fo.Form.echeck goal.g_env expr in
      CoreLogic.add_local (Location.unloc name, ty, Some expr) (parent##.proof, _self##.handle)

    in js_proof_engine (!!doit ())

  (* [this#move_hyp (from : handle<js_hyp>) (before : handle<js_hyp> option)] move
   * hypothesis [from] before hypothesis [before]. Both hypothesis
   * must be part of this sub-goal. *)
  method move_hyp from before =
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
  val form = js_form (parent##.handle, `H handle) hyp.h_form

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

  method getmeta =
    Js.Opt.option (Proof.get_meta _self##.proof##.proof _self##.handle)

  method setmeta meta =
    Proof.set_meta _self##.proof##.proof _self##.handle (Js.Opt.to_option meta)
end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for a local variable                                      *)
and js_tvar parent ((i, (handle, x, (ty, body))) : int * (Handle.t * Fo.vname * Fo.bvar)) =
object%js (_self)
  (* back-link to the [js_subgoal] this local variable belongs to *)
  val parent = parent

  (* the handle of the local variable *)
  val handle = handle

  (* the handle position in its context *)
  val position = i

  (* the local variable name *)
  val name = Js.string (Fo.e_tostring (EVar x))

  (* the local variable type as a [js_type] *)
  val type_ = js_type ty

  (* the local definition - return an optional expression *)
  val body =
    Js.Opt.option (Option.map js_expr body)

  (* The enclosing proof engine *)
  val proof = parent##.parent

  (* Return the [html] of the enclosed formula *)  
  method html =
    let open Tyxml in
    let open Utils.Xml in

    let id =
      Format.sprintf "%d/%d"
        (Handle.toint _self##.parent##.handle)
        (Handle.toint _self##.handle)
    in
    let dt =
      span [
        span ~a:[Xml.string_attrib "id" (id ^ ":")] begin
            [span [Xml.pcdata (UTF8.of_latin1 (Fo.e_tostring (EVar x)))]] @
            spaced_span [Xml.pcdata ":"] @
            [Fo.t_tohtml ty]
          @
          match body with
          | Some b ->
              spaced_span [Xml.pcdata ":="] @
              [Fo.e_tohtml ~id:(Some id) b]
          | None -> []
        end
      ]
    in Js.string (Format.asprintf "%a" (Tyxml.Xml.pp ()) dt)

  (* Return the [mathml] of the enclosed formula *)  
  method mathml =
    let open Tyxml in
    let open Utils.Xml in

    let id =
      Format.sprintf "%d/%d"
        (Handle.toint _self##.parent##.handle)
        (Handle.toint _self##.handle)
    in
    let dt =
      span [
        span ~a:[Xml.string_attrib "id" (id ^ ":")] begin
            [span [Xml.pcdata (UTF8.of_latin1 (Fo.e_tostring (EVar x)))]] @
            spaced_span [Xml.pcdata ":"] @
            [Fo.t_tomathml ty]
          @
          match body with
          | Some b ->
              spaced_span [Xml.pcdata ":="] @
              [Fo.e_tomathml ~id:(Some id) b]
          | None -> []
        end
      ]
    in Js.string (Format.asprintf "%a" (Tyxml.Xml.pp ()) dt)

  (* Return an UTF8 string representation of the enclosed formula *)
  method tostring =
    match body with
    | Some b ->
        Js.string (Format.sprintf "%s : %s := %s"
          (Fo.e_tostring (EVar x)) (Fo.t_tostring ty) (Fo.e_tostring b))
    | None ->
        Js.string (Format.sprintf "%s : %s"
          (Fo.e_tostring (EVar x)) (Fo.t_tostring ty))

  method getmeta =
    Js.Opt.option (Proof.get_meta _self##.proof##.proof _self##.handle)

  method setmeta meta =
    Proof.set_meta _self##.proof##.proof _self##.handle (Js.Opt.to_option meta)
end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for formulas                                              *)
and js_form (source : source) (form : Fo.form) = object%js (_self)
  (* Return the [mathml] of the formula *)  
  method mathml =
    _self##mathmltag true

  (* Return the [html] of the formula *)  
  method html =
    _self##htmltag true

  (* Return the [mathml] of the formula *)  
  method mathmltag (id : bool) =
    let prefix =
      if not id then None else Some (Some (
        match source with
        | h, `H i -> Format.sprintf "%d/%d" (Handle.toint h) (Handle.toint i)
        | h, `C   -> Format.sprintf "%d/0" (Handle.toint h)
      ))
    in
      Js.string
        (Format.asprintf "%a" (Tyxml.Xml.pp ())
        (Fo.f_tomathml ?id:prefix form))

  (* Return the [html] of the formula *)  
  method htmltag (id : bool) =
    let prefix =
      if not id then None else Some (Some (
        match source with
        | h, `H i -> Format.sprintf "%d/%d" (Handle.toint h) (Handle.toint i)
        | h, `C   -> Format.sprintf "%d/0" (Handle.toint h)
      ))
    in
      Js.string
        (Format.asprintf "%a" (Tyxml.Xml.pp ())
        (Fo.f_tohtml ?id:prefix form))

  (* Return an UTF8 string representation of the formula *)
  method tostring =
    Js.string (Fo.f_tostring form)
end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for expressions                                           *)
and js_expr (expr : Fo.expr) = object%js (_self)
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
      (Fo.e_tomathml expr))

  (* Return the [html] of the formula *)  
  method htmltag =
    Js.string
      (Format.asprintf "%a" (Tyxml.Xml.pp ())
      (Fo.e_tohtml expr))

  (* Return an UTF8 string representation of the expression *)
  method tostring =
    Js.string (Fo.e_tostring expr)
end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for formulas                                              *)
and js_type (ty : Fo.type_) = object%js (_self)
  (* Return the raw [mathml] of the type *)
  method rawmathml =
    Fo.t_tomathml ty

  (* Return the raw [html] of the type *)
  method rawhtml =
    Fo.t_tohtml ty

  (* Return the raw string representation of the type *)
  method rawstring =
    Fo.t_tostring ty

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
      let env, goal = !!(fun () ->
        let goal = String.trim (Js.to_string x) in
        let goal = Io.parse_goal (Io.from_string goal) in
        Fo.Goal.check goal
      ) () in js_proof_engine (Proof.init env goal)
  end)
