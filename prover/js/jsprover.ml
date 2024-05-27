(* -------------------------------------------------------------------- *)
open Utils.Pervasive
open Prover
open Api
open Logic
open Lang
open CoreLogic

(* -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
exception InvalidASource

(** Exception raised when the user tries to move (i.e. reorder) a local variable. 
    It is only allowed to move hypotheses. *)
exception MoveOnlyHyps of string

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
    match to_string (typeof v) with "string" -> to_string v | _ -> raise exn
end

(* -------------------------------------------------------------------- *)
let () =
  Exn.register
    begin
      fun exn ->
        match exn with
        (*| DuplicatedEntry (_, name) ->
              Some ("duplicated entry \"" ^ name ^ "\" in goal")
          | TypingError -> Some "invalid goal (typing error)"
          | RecheckFailure -> Some "invalid goal (recheck failure)"
          | Proof.Tactics.TacticNotApplicable -> Some "tactic not applicable"*)
        | MoveOnlyHyps name ->
            Some ("Reordering variables is not supported : " ^ name)
        | Typing.TypingError err ->
            Some ("Invalid goal (typing error)\n" ^ Typing.show_typeError err)
        | _ -> None
    end

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

let ipath_of_obj obj =
  obj |> Js.as_string InvalidASource |> Logic.Path.of_string

let ipath_of_array obj =
  obj |> Js.to_array |> Array.to_list |> List.map ipath_of_obj

let ipath_of_opt obj = obj |> Js.Opt.to_option |> Option.map ipath_of_obj

(* -------------------------------------------------------------------- *)
let rec js_proof_engine (proof : Proof.t) =
  object%js (_self)
    val proof = proof

    (* Return a [js_subgoal] array of all the opened subgoals *)
    method subgoals =
      let subgoals = Proof.opened proof in
      let subgoals = List.map (js_subgoal _self) subgoals in
      Js.array (Array.of_list subgoals)

    (* Return true when there are no opened subgoals left *)
    method closed = Js.bool (Proof.closed proof)

    (* Return the given action as a binary, base64-encoded string *)
    (*method getactionb action =
      let pr =
        action
        |> !!(Export.export_action (Proof.hidmap _self##.proof) _self##.proof)
      in
      js_log (Api.Logic.show_action pr);
      pr |> Fun.flip Marshal.to_string [] |> Base64.encode_string |> Js.string*)

    (* Get the meta-data attached to this proof engine *)
    method getmeta = Js.Opt.option (Proof.get_proof_meta proof)

    (* Attach meta-data to the proof engine *)
    method setmeta meta = Proof.set_proof_meta proof (Js.Opt.to_option meta)

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
      let open Actions in
      let actions =
        let kinds =
          match Js.to_string (Js.typeof asource) with
          | "string" -> [ Click (ipath_of_obj asource) ]
          | "object" -> (
              let asource = Js.Unsafe.coerce asource in
              match Js.as_string InvalidASource asource##.kind with
              | "click" ->
                  let path = ipath_of_obj asource##.path in
                  [ Click path ]
              | "ctxt" -> [ Ctxt ]
              | "dnd" ->
                  let source = ipath_of_obj asource##.source in
                  let destination = ipath_of_opt asource##.destination in
                  [ DnD (source, destination) ]
              | "any" ->
                  let path = ipath_of_obj asource##.path in
                  [ Click path; DnD (path, None) ]
              | _ -> raise InvalidASource)
          | _ -> raise InvalidASource
        and selection = ipath_of_array asource##.selection in

        let asource =
          List.map (fun kind -> Actions.{ kind; selection }) kinds
        in

        List.flatten (List.map !!(Actions.actions _self##.proof) asource)
      in

      Js.array
        (Array.of_list
           (List.map
              (fun Actions.
                     { description = p
                     ; icon = ic
                     ; highlights = ps
                     ; kind = aui
                     ; preaction = a
                     ; goal_id = g_id
                     } ->
                let ps = List.map Path.to_string ps in
                let ps = Js.array (Array.of_list (List.map Js.string ps)) in

                let aui =
                  match aui with
                  | Click p ->
                      Js.Unsafe.obj
                        [| ("kind", Js.Unsafe.inject (Js.string "click"))
                         ; ( "target"
                           , Js.Unsafe.inject (Js.string (Path.to_string p)) )
                        |]
                  | DnD (src, dst) ->
                      Js.Unsafe.obj
                        [| ("kind", Js.Unsafe.inject (Js.string "dnd"))
                         ; ( "source"
                           , Js.Unsafe.inject (Js.string (Path.to_string src))
                           )
                         ; ( "destination"
                           , Js.Unsafe.inject
                               (Js.string (Path.to_string @@ Option.get dst)) )
                        |]
                  | Ctxt ->
                      Js.Unsafe.obj
                        [| ("kind", Js.Unsafe.inject (Js.string "ctxt")) |]
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
                   ; ("action", Js.Unsafe.inject (g_id, a))
                  |])
              actions))

    (*(** [this#lemmareqb (selection : CoreLogic.IPath.t list) (pattern : string)] returns the base64-encoded string corresponding to the parameters of
             a lemma request, where [pattern] is the text entered in the lemma search bar and [selection] is the currently selected subformula. *)
      method lemmareqb selection pattern =
        let doit () =
          (* Convert the pattern from JS to ocaml. *)
          let pattern =
            pattern |> Js.Optdef.to_option
            |> Option.map (Js.as_string @@ Invalid_argument "Jsapi.filterlemmas")
            |> begin
                 function Some "" -> None | x -> x
               end
          in
          (* Convert the selection from JS to ocaml. *)
          let selection =
            match
              selection |> Js.Optdef.to_option |> Option.map ipath_of_array
            with
            | None -> None
            | Some [] -> None
            | Some [ selection ] -> Some selection
            | Some _ ->
                js_log
                  "Jsapi.lemmareqb : limited to one selection. Setting selection \
                   to None.";
                None
          in
          (* Get the sub-formula pointed at by the selection. *)
          let term =
            selection
            |> Option.map (CoreLogic.IPath.term _self##.proof)
            |> Option.map Fo.Translate.of_term
          in
          (* Encode the pattern and formula. *)
          ((pattern, term) : string option * Api.Logic.term option)
          |> Fun.flip Marshal.to_string []
          |> Base64.encode_string |> Js.string
        in
        !!doit ()

      (** Load the lemma database specified by the [data] object into the prover. *)
      method loadlemmas datab =
        (* Decode the data.
           The type annotation here is very important for unmarshaling to work. *)
        let (env, lemmas) : Api.Logic.lemmadb =
          datab |> Js.to_string |> Base64.decode_exn
          |> Fun.flip Marshal.from_string 0
        in
        (* Translate the lemmas and env to the actema format. *)
        let lemmas =
          List.map
            begin
              fun Api.Logic.{ l_user; l_full; l_stmt } ->
                Proof.{ l_user; l_full; l_form = Fo.Translate.to_form l_stmt }
            end
            lemmas
        in
        let env = Hidmap.State.run (Fo.Translate.to_env env) Hidmap.empty in
        (* Check the lemmas are all well-typed in the database environment. *)
        List.iter (fun lemma -> Fo.Form.recheck env lemma.Proof.l_form) lemmas;
        (* Create the lemma database. First we have to assign a handle to each lemma. *)
        let db =
          Proof.Lemmas.extend_env env
          @@ Proof.Lemmas.of_list
          @@ List.mapi (fun _ lemma -> (Handle.fresh (), lemma)) lemmas
        in
        (* Print debug info. *)
        js_log
        @@ Format.sprintf "Received lemmas (count=%d)\n" (List.length lemmas);
        (*List.iter (fun (name, _) -> js_log name) lemmas;*)
        (* Load the lemmas in the database. *)
        let new_proof = Proof.set_db _self##.proof db in
        js_proof_engine new_proof

      (** Serialize the current lemma database into a JS array.
             Returns an array of lemmas. Each lemma contains the following :
               (handle (int), name (string), pretty-printed-formula (string)).
             For performance reasons, we only return a limited amount of lemmas. *)
      method getlemmas =
        let db = _self##.proof |> Proof.get_db in
        db |> Proof.Lemmas.to_list |> List.take 100
        |> List.map
             begin
               fun (handle, lemma) ->
                 let handle =
                   handle |> Handle.toint |> string_of_int |> Js.string
                 in
                 let name = lemma.Proof.l_user |> Js.string in
                 let form =
                   Notation.f_tostring (Proof.Lemmas.env db) lemma.l_form
                   |> Js.string
                 in
                 Js.array [| handle; name; form |]
             end
        |> Array.of_list |> Js.array

      (** Filter the lemma database according to :
             - the current selection.
             - a text pattern (usually the text in the lemma search-bar's input-box).
             Both arguments are optional (in javascript-land, they can be undefined). *)
      method filterlemmas selection pattern =
        let open LemmaUtils in
        (* Convert the pattern from JS to ocaml. *)
        let pattern =
          pattern |> Js.Optdef.to_option
          |> Option.map (Js.as_string @@ Invalid_argument "Jsapi.filterlemmas")
        in
        (* Convert the selection from JS to ocaml. *)
        let selection =
          selection |> Js.Optdef.to_option |> Option.map ipath_of_array
        in
        (* Construct the filtering predicate. *)
        let pred =
          Pred.and_
            begin
              match pattern with
              | None | Some "" -> Pred.true_
              | Some pattern -> Pred.match_name pattern
            end
            begin
              match selection with
              | None | Some [] -> Pred.true_
              | Some [ selection ] ->
                  Pred.or_ (Pred.link_sfl selection)
                    (Pred.link_drewrite selection)
              | _ ->
                  failwith "Jsapi.filterlemmas: only supports a single selection."
            end
        in
        (* Filter the lemma database. *)
        let proof =
          Utils.time "filter-lemmas" @@ fun () -> filter pred _self##.proof
        in
        js_proof_engine proof*)
  end

(* -------------------------------------------------------------------- *)
(* JS wrapper for subgoals                                              *)
and js_subgoal parent (handle : int) =
  object%js (_self)
    (* back-link to the [js_proof_engine] this subgoal belongs to *)
    val parent = parent

    (* the handle (index) of the subgoal *)
    val handle = handle

    (* the OCaml subgoal *)
    method goal = Proof.byid parent##.proof _self##.handle

    (* Return all the local variables as a [js_tvar array] *)
    method tvars =
      (* let goal = _self##goal in
         let tvars = Vars.to_list goal.g_env in
         let aout =
           List.mapi (fun i (id, x, b) -> js_tvar _self (i, (id, x, b))) tvars
         in
         Js.array (Array.of_list aout)*)
      Js.array [||]

    (** Return all the local hypotheses (context) as a [js_hyps array] *)
    method context =
      let goal = _self##goal in
      let hyps = List.rev (Logic.Hyps.to_list goal.Logic.g_hyps) in
      Js.array (Array.of_list (List.mapi (js_hyps _self _self##.handle) hyps))

    (** Return the subgoal conclusion as a [js_form] *)
    method conclusion =
      let goal = Proof.byid parent##.proof _self##.handle in
      js_term _self _self##.handle `C goal.g_concl

    (** [this#ivariants] Return the available introduction rules that can
                be applied to the conclusion of [this] as a string array. The strings
                are only for documentation purposes - only their position in the
                returned array is meaningful and can be used as argument to [#intro]
                to select the desired introduction rule. *)
    method ivariants =
      (*let aout = !!Proof.Tactics.ivariants parent##.proof ~goal_id:handle in
        let aout = Array.of_list (List.map Js.string aout) in
        Js.array aout*)
      Js.array [||]

    (*(** [this#getduplicateb (hyp_handle : int)] gets the hypothesis in the current goal,
                  and returns the base64-encoded string of the corresponding ADuplicate action. *)
      method getduplicateb hyp_handle =
            let doit () =
              (* Get the hypothesis name. *)
              let hidmap = Proof.hidmap parent##.proof in
              let hyp_name = Hidmap.State.run (Hidmap.find hyp_handle) hidmap in
              (* Construct the ADuplicate action and encode it. *)
              Api.Logic.ADuplicate hyp_name
              |> Fun.flip Marshal.to_string []
              |> Base64.encode_string |> Js.string
            in
            !!doit ()

          (** [this#getclearb (hyp_handle : int)] gets the hypothesis in the current goal,
                 and returns the base64-encoded string of the corresponding AClear action. *)
          method getclearb hyp_handle =
            let doit () =
              (* Get the hypothesis name. *)
              let hidmap = Proof.hidmap parent##.proof in
              let hyp_name = Hidmap.State.run (Hidmap.find hyp_handle) hidmap in
              (* Construct the AClear action and encode it. *)
              Api.Logic.AClear hyp_name
              |> Fun.flip Marshal.to_string []
              |> Base64.encode_string |> Js.string
            in
            !!doit ()

          (** [this#getgeneralizeb (hyp_handle : int)] gets the hypothesis in the current goal,
                 and returns the base64-encoded string of the corresponding AGeneralize action. *)
          method getgeneralizeb hyp_handle =
            let doit () =
              (* Get the hypothesis name. *)
              let hidmap = Proof.hidmap parent##.proof in
              let hyp_name = Hidmap.State.run (Hidmap.find hyp_handle) hidmap in
              (* Construct the AClear action and encode it. *)
              Api.Logic.AGeneralize hyp_name
              |> Fun.flip Marshal.to_string []
              |> Base64.encode_string |> Js.string
            in
            !!doit ()

          (** [this#getcutb (form : string)] parses [form] in the current goal, and
                 returns the base64-encoded string of the corresponding ACut action. *)
          method getcutb form =
            let doit () =
              let goal = _self##goal in
              let form =
                form |> Js.to_string |> String.trim |> Io.from_string |> Io.parse_form
                |> Form.check goal.g_env |> Fo.Translate.of_form
              in
              Api.Logic.ACut form
              |> Fun.flip Marshal.to_string []
              |> Base64.encode_string |> Js.string
            in
            !!doit ()

          (** [this#addlemmab (handle : int)] return the base64-encoded string of the corresponding ALemma action. *)
          method addlemmab handle =
            let doit () =
              (* Find the lemma (and raise an exception if it is not found). *)
              let db = Proof.get_db parent##.proof in
              let lemma = Proof.Lemmas.byid db handle in
              js_log @@ Format.sprintf "addlemmab %s\n" lemma.l_full;
              (* Recheck the lemma just to make sure. *)
              Form.recheck (Proof.Lemmas.env db) lemma.l_form;
              (* Construct the action and encode it. *)
              Api.Logic.ALemma lemma.l_full
              |> Fun.flip Marshal.to_string []
              |> Base64.encode_string |> Js.string
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
              |> Fun.flip Marshal.to_string []
              |> Base64.encode_string |> Js.string
            in
            !!doit ()*)

    (** [this#move_hyp (from : string) (before : string option)] moves
        hypothesis [from] before hypothesis [before].
        Both hypotheses must be part of this sub-goal.
        Raises [InvalidHyphName] if [from] is not a hypothesis (for instance if it is a local variable). *)
    method movehyp from before =
      let doit () =
        let from = Name.make from in
        let before = Option.map Name.make @@ Js.Opt.to_option before in
        Js_log.log
        @@ Format.sprintf "Moving hyp [%s] to [%s]\n" (Name.show from)
             (Option.map_default Name.show "#None" before);
        let subgoal = Proof.byid parent##.proof _self##.handle in
        (* Check that [from] is a hypothesis. *)
        let is_hypothesis = List.mem from (Logic.Hyps.names subgoal.g_hyps) in
        if is_hypothesis
        then
          (* Actually move the hypothesis. *)
          Proof.move parent##.proof ~goal_id:_self##.handle ~hyp_name:from
            ~dest_name:before
        else raise @@ MoveOnlyHyps (Name.show from)
      in
      js_proof_engine (!!doit ())

    method getmeta =
      Js.Opt.option (Proof.get_goal_meta parent##.proof ~goal_id:_self##.handle)

    method setmeta meta =
      Proof.set_goal_meta parent##.proof ~goal_id:_self##.handle
        (Js.Opt.to_option meta)

    (*method toascii =
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
        let concl : string =
          _self##conclusion |> fun c -> c##toascii |> Js.to_string
        in

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

        Js.string
          (Printf.sprintf "%s; %s |- %s"
             (comma [ funs; vars; props ])
             (to_string hyps) concl)

      method tostring =
        let hyps : string list =
          _self##context |> Js.to_array |> Array.to_list
          |> List.map (fun h -> h##tostring |> Js.to_string)
        in
        let concl : string =
          _self##conclusion |> fun c -> c##tostring |> Js.to_string
        in

        let to_string = List.to_string ~sep:", " ~left:"" ~right:"" identity in

        Js.string (Printf.sprintf "%s ⊢ %s" (to_string hyps) concl)*)
  end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for a context hypothesis                                  *)
and js_hyps parent (goal_id : int) (pos : int) (hyp : Logic.hyp) =
  object%js (_self)
    (* back-link to the [js_subgoal] this hypothesis belongs to *)
    val parent = parent

    (* the handle (UID) of the hypothesis *)
    val handle = Js.string @@ Name.show hyp.h_name

    (* the handle (UID) of the parent hypothesis *)
    val phandle = Js.Opt.option @@ Some (Name.show hyp.h_name)

    (* the handle position in its context *)
    val position = pos

    (* if the hypothesis is fresh / new *)
    val fresh = Js.bool (hyp.h_gen <= 1)

    (* the hypothesis as a [js_term] *)
    val term = js_term parent parent##.handle (`H hyp.h_name) hyp.h_form

    (* The enclosing proof engine *)
    val proof = parent##.parent

    (* Return the [html] of the enclosed formula *)
    method html = _self##.term##html

    (* Return an UTF8 string representation of the enclosed formula *)
    method tostring = _self##.term##tostring

    method getmeta =
      Js.Opt.option
        (Proof.get_hyp_meta _self##.proof##.proof ~goal_id ~hyp_name:hyp.h_name)

    method setmeta meta =
      Proof.set_hyp_meta
        _self##.proof##.proof
        ~goal_id ~hyp_name:hyp.h_name (Js.Opt.to_option meta)
  end

(* (* -------------------------------------------------------------------- *)
   (* JS Wrapper for a local variable                                      *)
   and js_tvar parent ((i, (handle, x, (ty, b))) : int * (Handle.t * vname * bvar))
       =
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
                     @ [ Notation.e_tohtml
                           ~id:(Some _self##idbody)
                           (parent##goal).g_env b
                       ]
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
                     @ [ Notation.e_tomathml
                           ~id:(Some _self##idbody)
                           (parent##goal).g_env b
                       ]
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

       method getmeta =
         Js.Opt.option (Proof.get_meta _self##.proof##.proof _self##.handle)

       method setmeta meta =
         Proof.set_meta
           _self##.proof##.proof
           _self##.handle (Js.Opt.to_option meta)
     end*)

(* -------------------------------------------------------------------- *)
(* JS Wrapper for terms                                              *)
and js_term parent (goal_id : int) (kind : [ `C | `H of Name.t ])
    (term : Term.t) =
  object%js (_self)
    (** Return the html of the term. *)
    method html =
      (* Get the path to the term. *)
      let path =
        match kind with
        | `H name -> Logic.Path.make ~kind:(Hyp name) goal_id
        | `C -> Logic.Path.make ~kind:Concl goal_id
      in
      (* Pretty-print the term to xml.
         We choose an arbitrary width here : in the future we could
         make it so this method takes the width as input, so that
         the javascript code decides which width to use. *)
      let xml =
        Notation.term_to_xml ~width:50 path (parent##goal).Logic.g_env term
      in
      (* For some reason the frontend requires us to :
         - wrap every string (pcdata) in a span.
         - wrap the whole term in a span.
         The frontend being in a horrible state, we comply
         and don't touch to the javascript code. *)
      let open Tyxml in
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
      let xml = span @@ add_spans xml in
      (* Pretty-print the xml to a string. This will then be used
         by the javascript code. *)
      Js.string @@ Format.asprintf "%a" (Tyxml.Xml.pp ()) xml

    (* Return an UTF8 string representation of the term. *)
    method tostring =
      Js.string (Notation.term_to_string (parent##goal).g_env term)
  end

(** Print a single goal in Actema format (for debug purposes). *)
let print_goal (Logic.{ g_id; g_pregoal = goal } : Logic.goal) : unit =
  let xml = Notation.term_to_xml (Logic.Path.make 0) goal.g_env goal.g_concl in
  Js_log.log @@ Format.asprintf "%a\n" (Tyxml.Xml.pp ()) xml

(* Print the env. *)
(*js_log "ENV\n";
  List.iter
    begin
      fun (name, ty) ->
        js_log
        @@ Format.sprintf "%s : %s\n" (Name.show name)
             (Notation.term_to_string goal.g_env ty)
    end
    (Name.Map.bindings goal.g_env.constants);
  (* Print the hypotheses. *)
  js_log "HYPS\n";
  Logic.Hyps.iter
    begin
      fun hyp ->
        js_log
        @@ Format.sprintf "%s : %s\n" (Name.show hyp.h_name)
             (Notation.term_to_string goal.g_env hyp.h_form)
    end
    goal.g_hyps;
  (* Print the conclusion. *)
  js_log
  @@ Format.sprintf "GOAL\n%s\n"
       (Notation.term_to_string goal.g_env goal.g_concl)*)

(* -------------------------------------------------------------------- *)
let export (name : string) : unit =
  Js.export name
    (object%js
       (* Return a new proof engine whose goals are the base64, binary decoding of [goalsb]  *)
       method setgoalsb goalsb =
         let goals : Logic.goal list =
           goalsb |> Js.to_string |> Base64.decode_exn
           |> Fun.flip Marshal.from_string 0
         in
         (*let hm = List.fold_left Hidmap.union Hidmap.empty hms in*)
         (* Log the goals. *)
         List.iter print_goal goals;
         (* Create a new proof engine. *)
         js_proof_engine (!!Proof.init goals)
    end)

(* -------------------------------------------------------------------- *)
let () = export "engine"
