(* -------------------------------------------------------------------- *)
open Utils
open Fo

(* -------------------------------------------------------------------- *)
type source = Handle.t * [ `C | `H of Handle.t ]

(* -------------------------------------------------------------------- *)
exception InvalidASource
exception InvalidLemmaDB

(* -------------------------------------------------------------------- *)
module Exn : sig
  val register : (exn -> string option) -> unit
  val translate : exn -> string option
end = struct
  type tx_t = exn -> string option

  let translators = ref ([] : tx_t list)
  let register (tx : tx_t) : unit = translators := !translators @ [ tx ]

  let translate (e : exn) =
    let module E = struct
      exception Found of string
    end in
    try
      List.iter (fun tx -> tx e |> Option.may (fun msg -> raise (E.Found msg))) !translators;
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
    match to_string (typeof v) with "string" -> to_string v | _ -> raise exn
end

(* -------------------------------------------------------------------- *)
let () =
  Exn.register (fun exn ->
      match exn with
      | Syntax.ParseError _ -> Some "invalid input (parse error)"
      | DuplicatedEntry (_, name) -> Some ("duplicated entry \"" ^ name ^ "\" in goal")
      | TypingError -> Some "invalid goal (typing error)"
      | RecheckFailure -> Some "invalid goal (recheck failure)"
      | Proof.Tactics.TacticNotApplicable -> Some "tactic not applicable"
      | _ -> None)

(* -------------------------------------------------------------------- *)
let ( !! ) f x =
  try f x
  with e ->
    let msg =
      Option.default_delayed
        (fun () -> Format.sprintf "internal error: %s" (Printexc.to_string e))
        (Exn.translate e)
    in
    Js.Js_error.(raise_ (of_error (new%js Js.error_constr (Js.string msg))))

let ipath_of_obj obj = obj |> Js.as_string InvalidASource |> CoreLogic.IPath.of_string
let ipath_of_array obj = obj |> Js.to_array |> Array.to_list |> List.map ipath_of_obj
let ipath_of_opt obj = obj |> Js.Opt.to_option |> Option.map ipath_of_obj

(* -------------------------------------------------------------------- *)
let rec js_proof_engine (proof : Proof.proof) =
  object%js (_self)
    val proof = proof
    val handle = Handle.fresh ()

    (* Return a [js_subgoal] array of all the opened subgoals *)
    method subgoals =
      let subgoals = Proof.opened proof in
      let subgoals = List.map (js_subgoal _self) subgoals in
      Js.array (Array.of_list subgoals)

    (* Return true when there are no opened subgoals left *)
    method closed = Js.bool (Proof.closed proof)

    (* Return the given action as a binary, base64-encoded string *)
    method getactionb action =
      let pr = action |> !!(Export.export_action (Proof.hidmap _self##.proof) _self##.proof) in
      js_log (Api.Logic.show_action pr);
      pr |> Fun.flip Marshal.to_string [] |> Base64.encode_string |> Js.string

    (* Get the meta-data attached to this proof engine *)
    method getmeta = Js.Opt.option (Proof.get_meta proof _self##.handle)

    (* Attach meta-data to the proof engine *)
    method setmeta meta = Proof.set_meta proof _self##.handle (Js.Opt.to_option meta)

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
     *  - action      : the related action
     *)
    method actions asource =
      let actions =
        let kinds =
          match Js.to_string (Js.typeof asource) with
          | "string" -> [ `Click (ipath_of_obj asource) ]
          | "object" -> (
              let asource = Js.Unsafe.coerce asource in
              match Js.as_string InvalidASource asource##.kind with
              | "click" ->
                  let path = ipath_of_obj asource##.path in
                  [ `Click path ]
              | "ctxt" -> [ `Ctxt ]
              | "dnd" ->
                  let source = ipath_of_obj asource##.source in
                  let destination = ipath_of_opt asource##.destination in
                  [ `DnD Link.{ source; destination } ]
              | "any" ->
                  let path = ipath_of_obj asource##.path in
                  [ `Click path; `DnD Link.{ source = path; destination = None } ]
              | _ -> raise InvalidASource)
          | _ -> raise InvalidASource
        and selection = ipath_of_array asource##.selection in

        let asource = List.map (fun kind -> Link.{ kind; selection }) kinds in

        List.flatten (List.map !!(Link.actions _self##.proof) asource)
      in

      Js.array
        (Array.of_list
           (List.map
              (fun Link.{ description = p; icon = ic; highlights = ps; kind = aui; action = a } ->
                let ps = List.map CoreLogic.IPath.to_string ps in
                let ps = Js.array (Array.of_list (List.map Js.string ps)) in

                let aui =
                  let pp = CoreLogic.IPath.to_string in

                  match aui with
                  | `Click p ->
                      Js.Unsafe.obj
                        [| ("kind", Js.Unsafe.inject (Js.string "click"))
                         ; ("target", Js.Unsafe.inject (Js.string (pp p)))
                        |]
                  | `DnD (src, dst) ->
                      Js.Unsafe.obj
                        [| ("kind", Js.Unsafe.inject (Js.string "dnd"))
                         ; ("source", Js.Unsafe.inject (Js.string (pp src)))
                         ; ("destination", Js.Unsafe.inject (Js.string (pp dst)))
                        |]
                  | `Ctxt -> Js.Unsafe.obj [| ("kind", Js.Unsafe.inject (Js.string "ctxt")) |]
                in

                let icon =
                  match ic with
                  | Some s -> Js.Unsafe.inject (Js.string s)
                  | None -> Js.Unsafe.inject Js.undefined
                in

                Js.Unsafe.obj
                  [| ("description", Js.Unsafe.inject (Js.string p))
                   ; ("icon", icon)
                   ; ("highlight", Js.Unsafe.inject ps)
                   ; ("ui", aui)
                   ; ("action", Js.Unsafe.inject a)
                  |])
              actions))

    (** Same as [actions], but in async mode. TO BE TESTED *)
    method pactions path =
      let%lwt _ = Lwt.return () in
      Lwt.return (_self##actions path)

    (** [this#lemmareqb (pattern : string) (selection : )] returns the base64-encoded string corresponding to the parameters of
        a lemma request, where [pattern] is the text entered in the lemma search bar and [selection] is the currently selected subformula. *)
    method lemmareqb _pattern _selection =
      let doit () =
        let pattern = Some "PATTERN_TEST" in
        let form = Some (Api.Logic.FPred ("FORM_TEST", [])) in
        ((pattern, form) : string option * Api.Logic.form option)
        |> Fun.flip Marshal.to_string [] |> Base64.encode_string |> Js.string
      in
      !!doit ()

    (** Load the lemma database specified by the [data] object into the prover. *)
    method loadlemmas datab =
      (* Decode the data.
         The type annotation here is very important for unmarshaling to work. *)
      let (env, lemmas) : Api.Logic.lemmadb =
        Utils.time "decode-lemmas" @@ fun () ->
        datab |> Js.to_string |> Base64.decode_exn |> Fun.flip Marshal.from_string 0
      in
      (* Translate the lemmas and env to the actema format. *)
      let lemmas =
        Utils.time "translate-lemmas" @@ fun () ->
        List.map
          begin
            fun Api.Logic.{ l_user; l_full; l_stmt } ->
              (l_full, (l_user, Fo.Translate.to_form l_stmt))
          end
          lemmas
      in
      let env =
        Utils.time "translate-env" @@ fun () ->
        Hidmap.State.run (Fo.Translate.to_env env) Hidmap.empty
      in
      (* Check the lemmas are all well-typed in the database environment. *)
      Utils.time "type-check-lemmas" @@ fun () ->
      List.iter (fun (_, (_, form)) -> Fo.Form.recheck env form) lemmas;
      (* Create the lemma database. *)
      let db = Proof.{ db_env = env; db_map = Map.of_seq @@ List.to_seq lemmas } in
      (* Print debug info. *)
      js_log @@ Format.sprintf "Received lemmas (count=%d)\n" (List.length lemmas);
      (*List.iter (fun (name, _) -> js_log name) lemmas;*)
      (* Load the lemmas in the database. *)
      let new_proof = Proof.set_db _self##.proof db in
      js_proof_engine new_proof

    (** Serialize the current lemma database into a JS array. 
        Returns an array of lemmas. Each lemma contains three strings : (full-name, user-name, pretty-printed-formula) *)
    method getlemmas =
      let db = _self##.proof |> Proof.get_db in
      db.db_map |> Map.bindings
      |> List.map
           begin
             fun (full_name, (user_name, form)) ->
               let full_name = full_name |> Js.string in
               let user_name = user_name |> Js.string in
               let stmt = Notation.f_tostring db.db_env form |> Js.string in
               Js.array [| full_name; user_name; stmt |]
           end
      |> Array.of_list |> Js.array

    (** Filter the lemma database according to :
        - the current selection.
        - a text pattern (usually the text in the lemma search-bar's input-box). 
        Both arguments are optional (in javascript-land, they can be undefined). *)
    method filterlemmas selection pattern =
      (* Convert the pattern from JS to ocaml. *)
      let pattern =
        pattern |> Js.Optdef.to_option
        |> Option.map (Js.as_string @@ Invalid_argument "Jsapi.filterlemmas")
      in
      js_log @@ Format.sprintf "Got pattern: %s\n" (Option.default "[none]" pattern);
      (* Convert the selection from JS to ocaml. *)
      let selection = selection |> Js.Optdef.to_option |> Option.map ipath_of_array in
      (* Get the proof. *)
      let proof = _self##.proof in
      (* Fitler by name. *)
      let proof =
        match pattern with None -> proof | Some pattern -> LemmaDB.filter_by_name pattern proof
      in
      (* Fiter by selection. *)
      let proof =
        match selection with
        | None | Some [] -> proof
        | Some [ selection ] -> LemmaDB.filter_by_selection selection proof
        | _ -> failwith "Jsapi.filterlemmas: only supports a single selection."
      in
      js_proof_engine proof
  end

(* -------------------------------------------------------------------- *)
(* JS wrapper for subgoals                                              *)
and js_subgoal parent (handle : Handle.t) =
  object%js (_self)
    (* back-link to the [js_proof_engine] this subgoal belongs to *)
    val parent = parent

    (* the handle (UID) of the subgoal *)
    val handle = handle

    (* the OCaml subgoal *)
    method goal = Proof.byid parent##.proof _self##.handle

    (* Return all the functional variables as a [string array] *)
    method fvars =
      let goal = _self##goal in
      let fvars : string list =
        Funs.all goal.g_env |> Map.bindings
        |> List.map (fun (f, (ar, res)) ->
               let ar =
                 List.to_string ~sep:" & " ~left:"" ~right:""
                   (Notation.t_tostring goal.Proof.g_env)
                   ar
               in
               let res = Notation.t_tostring goal.g_env res in
               Printf.sprintf "%s : %s -> %s" f ar res)
      in
      Js.array (Array.of_list (List.map Js.string fvars))

    (* Return all the propositional variables as a [string array] *)
    method pvars =
      let goal = _self##goal in
      let pvars = List.fst (Map.bindings (Prps.all goal.g_env)) in
      Js.array (Array.of_list (List.map Js.string pvars))

    (* Return all the local variables as a [js_tvar array] *)
    method tvars =
      let goal = _self##goal in
      let tvars = Vars.to_list goal.g_env in
      let aout = List.mapi (fun i (id, x, b) -> js_tvar _self (i, (id, x, b))) tvars in
      Js.array (Array.of_list aout)

    (** Return all the local hypotheses (context) as a [js_hyps array] *)
    method context =
      let goal = _self##goal in
      let hyps = List.rev (Proof.Hyps.to_list goal.g_hyps) in

      Js.array (Array.of_list (List.mapi (fun i x -> js_hyps _self (i, x)) hyps))

    (** Return the subgoal conclusion as a [js_form] *)
    method conclusion =
      let goal = Proof.byid parent##.proof _self##.handle in
      js_form _self (_self##.handle, `C) goal.g_goal

    (** [this#ivariants] Return the available introduction rules that can
        be applied to the conclusion of [this] as a string array. The strings
        are only for documentation purposes - only their position in the
        returned array is meaningful and can be used as argument to [#intro]
        to select the desired introduction rule. *)
    method ivariants =
      let aout = !!Proof.Tactics.ivariants parent##.proof ~goal_id:handle in
      let aout = Array.of_list (List.map Js.string aout) in
      Js.array aout

    (** [this#getcutb (form : string)] parses [form] in the current goal, and
        returns the base64-encoded string of the corresponding ACut action. *)
    method getcutb form =
      let doit () =
        let goal = _self##goal in
        let form =
          form |> Js.to_string |> String.trim |> Io.from_string |> Io.parse_form
          |> Form.check goal.g_env |> Fo.Translate.of_form
        in
        Api.Logic.ACut form |> Fun.flip Marshal.to_string [] |> Base64.encode_string |> Js.string
      in
      !!doit ()

    (** [this#addlemmab (full_name : string)] return the base64-encoded string of the corresponding ALemma action. *)
    method addlemmab full_name =
      let doit () =
        let full_name = Js.to_string full_name in
        js_log @@ Format.sprintf "addlemmab %s\n" full_name;
        (* Check the lemma database contains the lemma name (and raise LemmaNotFound if it doesn't),
           and recheck the lemma's statement (just to make sure). *)
        let db = Proof.get_db parent##.proof in
        let _, stmt =
          Option.get_exn
            (Map.find_opt full_name db.db_map)
            (Failure ("lemma not found " ^ full_name))
        in
        Form.recheck db.db_env stmt;
        js_log "recheck ok\n";
        (* Construct the action and encode it. *)
        Api.Logic.ALemma full_name |> Fun.flip Marshal.to_string [] |> Base64.encode_string
        |> Js.string
      in
      !!doit ()

    (** [this#add_local (name : string) (expr : string)] parses [expr] in the goal
        [context] and adds it to the local [context] under the name [name]. *)
    method addlocal name expr =
      let doit () =
        let goal = _self##goal in
        let expr = String.trim (Js.to_string expr) in
        let expr = Io.parse_expr (Io.from_string expr) in
        let expr, ty = Form.echeck goal.g_env expr in
        Proof.Tactics.add_local_def parent##.proof ~goal_id:_self##.handle
          (Js.to_string name, ty, expr)
      in
      js_proof_engine (!!doit ())

    (** [this#add_alias (nexpr : string)] parses [nexpr] as a named expression
        in the goal [context] and add it to the local [context]. *)
    method addalias expr =
      let doit () =
        let goal = _self##goal in
        let expr = String.trim (Js.to_string expr) in
        let name, expr = Io.parse_nexpr (Io.from_string expr) in
        let expr, ty = Form.echeck goal.g_env expr in
        Proof.Tactics.add_local_def parent##.proof ~goal_id:_self##.handle
          (Location.unloc name, ty, expr)
      in
      js_proof_engine (!!doit ())

    (** [this#getaliasb (nexpr : string)] parses [nexpr] as a named expression
        in the current goal, and returns the base64-encoded string of the
        corresponding ADef action. *)
    method getaliasb expr =
      let doit () =
        let goal = _self##goal in
        let expr = String.trim (Js.to_string expr) in
        let name, expr = Io.parse_nexpr (Io.from_string expr) in
        let expr, ty = Form.echeck goal.g_env expr in
        let name = Location.unloc name in
        let expr, ty = Fo.Translate.(of_expr expr, of_type_ ty) in
        Api.Logic.ADef (name, ty, expr)
        |> Fun.flip Marshal.to_string [] |> Base64.encode_string |> Js.string
      in
      !!doit ()

    (** [this#move_hyp (from : handle<js_hyp>) (before : handle<js_hyp> option)] move
        hypothesis [from] before hypothesis [before]. Both hypothesis
        must be part of this sub-goal. *)
    method movehyp from before =
      let doit () =
        Proof.Tactics.move parent##.proof ~goal_id:_self##.handle ~hyp_id:from
          ~dest_id:(Js.Opt.to_option before)
      in
      js_proof_engine (!!doit ())

    (** [this#generalize (h : handle<js_hyps>)] generalizes the hypothesis [h] *)
    method generalize hid =
      let doit () = Proof.Tactics.generalize parent##.proof ~goal_id:_self##.handle ~hyp_id:hid in
      js_proof_engine (!!doit ())

    method getmeta = Js.Opt.option (Proof.get_meta parent##.proof _self##.handle)
    method setmeta meta = Proof.set_meta parent##.proof _self##.handle (Js.Opt.to_option meta)

    method toascii =
      let funs : string list =
        _self##fvars |> Js.to_array |> Array.to_list |> List.map Js.to_string
      in
      let props : string list =
        _self##pvars |> Js.to_array |> Array.to_list |> List.map Js.to_string
      in
      let vars : string list =
        _self##tvars |> Js.to_array |> Array.to_list
        |> List.map (fun v -> v##toascii |> Js.to_string)
      in
      let hyps : string list =
        _self##context |> Js.to_array |> Array.to_list
        |> List.map (fun h -> h##toascii |> Js.to_string)
      in
      let concl : string = _self##conclusion |> fun c -> c##toascii |> Js.to_string in

      let to_string = List.to_string ~sep:", " ~left:"" ~right:"" identity in
      let comma =
        ""
        |> List.fold_left (fun s l ->
               if String.is_empty s
               then if List.is_empty l then "" else to_string l
               else if List.is_empty l
               then s
               else s ^ ", " ^ to_string l)
      in

      Js.string (Printf.sprintf "%s; %s |- %s" (comma [ funs; vars; props ]) (to_string hyps) concl)

    method tostring =
      let hyps : string list =
        _self##context |> Js.to_array |> Array.to_list
        |> List.map (fun h -> h##tostring |> Js.to_string)
      in
      let concl : string = _self##conclusion |> fun c -> c##tostring |> Js.to_string in

      let to_string = List.to_string ~sep:", " ~left:"" ~right:"" identity in

      Js.string (Printf.sprintf "%s ⊢ %s" (to_string hyps) concl)
  end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for a context hypothesis                                  *)
and js_hyps parent ((i, (handle, hyp)) : int * (Handle.t * Proof.hyp)) =
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
    method html = _self##.form##html

    (* Return the [mathml] of the enclosed formula *)
    method mathml = _self##.form##mathml

    (* Return an UTF8 string representation of the enclosed formula *)
    method tostring = _self##.form##tostring

    (* Return an ASCII string representation of the enclosed formula *)
    method toascii = _self##.form##toascii
    method getmeta = Js.Opt.option (Proof.get_meta _self##.proof##.proof _self##.handle)

    method setmeta meta =
      Proof.set_meta _self##.proof##.proof _self##.handle (Js.Opt.to_option meta)
  end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for a local variable                                      *)
and js_tvar parent ((i, (handle, x, (ty, b))) : int * (Handle.t * vname * bvar)) =
  object%js (_self)
    (* back-link to the [js_subgoal] this local variable belongs to *)
    val parent = parent

    (* the handle of the local variable *)
    val handle = handle

    (* the handle position in its context *)
    val position = i

    (* the local variable name, as an OCaml string *)
    val oname = Notation.e_tostring (parent##goal).g_env (EVar x)

    (* the local variable name *)
    method name = Js.string _self##.oname

    (* the local variable type as a [js_type] *)
    val type_ = js_type parent ty

    (* the local definition - return an optional expression *)
    val body = Js.Opt.option (Option.map (js_expr parent) b)

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
        span
          [ span
              ([ span
                   ~a:[ Xml.string_attrib "id" _self##idhead ]
                   ([ span [ Xml.pcdata _self##.oname ] ]
                   @ spaced [ span [ Xml.pcdata ":" ] ]
                   @ [ Notation.t_tohtml (parent##goal).g_env ty ])
               ]
              @
              match b with
              | Some b ->
                  spaced [ span [ Xml.pcdata ":=" ] ]
                  @ [ Notation.e_tohtml ~id:(Some _self##idbody) (parent##goal).g_env b ]
              | None -> [])
          ]
      in
      Js.string (Format.asprintf "%a" (Tyxml.Xml.pp ()) dt)

    (* Return the [mathml] of the enclosed local variable *)
    method mathml =
      let open Tyxml in
      let open Utils.Mathml in
      let dt =
        math
          [ row
              ([ row
                   ~a:[ Xml.string_attrib "id" _self##idhead ]
                   ([ mi (Notation.e_tostring (parent##goal).g_env (EVar x)) ]
                   @ [ mo ":" ]
                   @ [ Notation.t_tomathml (parent##goal).g_env ty ])
               ]
              @
              match b with
              | Some b ->
                  [ mo ":=" ]
                  @ [ Notation.e_tomathml ~id:(Some _self##idbody) (parent##goal).g_env b ]
              | None -> [])
          ]
      in
      Js.string (Format.asprintf "%a" (Tyxml.Xml.pp ()) dt)

    (* Return an UTF8 string representation of the enclosed local variable *)
    method tostring =
      match b with
      | Some b ->
          Js.string
            (Format.sprintf "%s : %s := %s"
               (Notation.e_tostring (parent##goal).g_env (EVar x))
               (Notation.t_tostring (parent##goal).g_env ty)
               (Notation.e_tostring (parent##goal).g_env b))
      | None ->
          Js.string
            (Format.sprintf "%s : %s"
               (Notation.e_tostring (parent##goal).g_env (EVar x))
               (Notation.t_tostring (parent##goal).g_env ty))

    (* Return an ASCII string representation of the enclosed local variable *)
    method toascii =
      match b with
      | Some b ->
          Js.string
            (Format.sprintf "%s := %s"
               (Notation.e_tostring (parent##goal).g_env (EVar x))
               (Notation.e_toascii (parent##goal).g_env b))
      | None ->
          Js.string
            (Format.sprintf "%s : %s"
               (Notation.e_tostring (parent##goal).g_env (EVar x))
               (Notation.t_toascii (parent##goal).g_env ty))

    method getmeta = Js.Opt.option (Proof.get_meta _self##.proof##.proof _self##.handle)

    method setmeta meta =
      Proof.set_meta _self##.proof##.proof _self##.handle (Js.Opt.to_option meta)
  end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for formulas                                              *)
and js_form parent (source : source) (form : form) =
  object%js (_self)
    (* The prefix for all subpaths of the formula *)
    val prefix =
      match source with
      | h, `H i -> Format.sprintf "%d/H#%d" (Handle.toint h) (Handle.toint i)
      | h, `C -> Format.sprintf "%d/C#0" (Handle.toint h)

    (* Return the [mathml] of the formula *)
    method mathml = _self##mathmltag true

    (* Return the [html] of the formula *)
    method html = _self##htmltag true

    (* Return the [mathml] of the formula *)
    method mathmltag (id : bool) =
      let prefix = if not id then None else Some _self##.prefix in
      Js.string
        (Format.asprintf "%a" (Tyxml.Xml.pp ())
           (Utils.Mathml.math [ Notation.f_tomathml (parent##goal).g_env ~id:prefix form ]))

    (* Return the [html] of the formula *)
    method htmltag (id : bool) =
      let prefix = if not id then None else Some _self##.prefix in
      Js.string
        (Format.asprintf "%a" (Tyxml.Xml.pp ())
           (Notation.f_tohtml (parent##goal).g_env ~id:prefix form))

    (* Return an UTF8 string representation of the formula *)
    method tostring = Js.string (Notation.f_tostring (parent##goal).g_env form)

    (* Return an ASCII string representation of the formula *)
    method toascii = Js.string (Notation.f_toascii (parent##goal).g_env form)
  end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for expressions                                           *)
and js_expr parent (expr : expr) =
  object%js (_self)
    (* Return the [mathml] of the formula *)
    method mathml = _self##mathmltag

    (* Return the [html] of the formula *)
    method html = _self##htmltag

    (* Return the [mathml] of the formula *)
    method mathmltag =
      Js.string
        (Format.asprintf "%a" (Tyxml.Xml.pp ())
           (Utils.Mathml.math [ Notation.e_tomathml (parent##goal).g_env expr ]))

    (* Return the [html] of the formula *)
    method htmltag =
      Js.string
        (Format.asprintf "%a" (Tyxml.Xml.pp ()) (Notation.e_tohtml (parent##goal).g_env expr))

    (* Return an UTF8 string representation of the expression *)
    method tostring = Js.string (Notation.e_tostring (parent##goal).g_env expr)
  end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for types                                                 *)
and js_type parent (ty : type_) =
  object%js (_self)
    (* Return the raw [mathml] of the type *)
    method rawmathml = Utils.Mathml.math [ Notation.t_tomathml (parent##goal).g_env ty ]

    (* Return the raw [html] of the type *)
    method rawhtml = Notation.t_tohtml (parent##goal).g_env ty

    (* Return the raw string representation of the type *)
    method rawstring = Notation.t_tostring (parent##goal).g_env ty

    (* Return the [mathml] of the type *)
    method mathml = Js.string (Format.asprintf "%a" (Tyxml.Xml.pp ()) _self##rawmathml)

    (* Return the [html] of the type *)
    method html = Js.string (Format.asprintf "%a" (Tyxml.Xml.pp ()) _self##rawhtml)

    (* Return an UTF8 string representation of the formula *)
    method tostring = Js.string _self##rawstring
  end

(* -------------------------------------------------------------------- *)
let export (name : string) : unit =
  Js.export name
    (object%js
       (* [this#parse input] parse the goal [input] and return a
        * [js_proof_engine] for it.
        *
        * Raise an exception if [input] is invalid *)
       method parse x =
         let env, hyps, goal =
           !!(fun () ->
               let goal = String.trim (Js.to_string x) in
               let goal = Io.parse_goal (Io.from_string goal) in
               Goal.check goal)
             ()
         in
         js_proof_engine (Proof.init env hyps goal)

       (* [this#parseToUnicode input] parses the goal [input] and returns
        * its unicode representation.
        *
        * Raise an exception if [input] is invalid *)
       method parseToUnicode x =
         let env, hyps, goal =
           !!(fun () ->
               let goal = String.trim (Js.to_string x##.input) in
               let goal = Io.parse_goal (Io.from_string goal) in
               Goal.check goal)
             ()
         in

         Js.string
           (Printf.sprintf "%s⊢ %s"
              (Js.Optdef.case x##.printHyps
                 (fun _ -> "")
                 (fun b ->
                   if not (Js.to_bool b)
                   then ""
                   else List.to_string ~sep:", " ~left:"" ~right:" " (Notation.f_tostring env) hyps))
              (Notation.f_tostring env goal))

       (* Return a new proof engine whose goals are the base64, binary decoding of [goalsb]  *)
       method setgoalsb goalsb =
         let goals : Api.Logic.goals =
           goalsb |> Js.to_string |> Base64.decode_exn |> Fun.flip Marshal.from_string 0
         in
         let gls, hms = goals |> !!(List.map Proof.Translate.import_goal) |> List.split in
         let hm = List.fold_left Hidmap.union Hidmap.empty hms in
         js_proof_engine (!!(Proof.ginit hm) gls)
    end)
