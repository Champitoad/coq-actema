(* -------------------------------------------------------------------- *)
open Prover
open Utils
open Fo

(* -------------------------------------------------------------------- *)
type source = Handle.t * [ `C | `H of Handle.t ]

(* -------------------------------------------------------------------- *)
exception InvalidASource
exception MoveOnlyHyps

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
      | MoveOnlyHyps -> Some "reordering variables is not supported"
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
                  [ `DnD Actions.{ source; destination } ]
              | "any" ->
                  let path = ipath_of_obj asource##.path in
                  [ `Click path; `DnD Actions.{ source = path; destination = None } ]
              | _ -> raise InvalidASource)
          | _ -> raise InvalidASource
        and selection = ipath_of_array asource##.selection in

        let asource = List.map (fun kind -> Actions.{ kind; selection }) kinds in

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
                     ; action = a
                     ; goal_handle = g_id
                     } ->
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
                   ; ("action", Js.Unsafe.inject (g_id, a))
                  |])
              actions))

    (** Same as [actions], but in async mode. TO BE TESTED *)
    method pactions path =
      let%lwt _ = Lwt.return () in
      Lwt.return (_self##actions path)

    (** [this#lemmareqb (selection : CoreLogic.IPath.t list) (pattern : string)] returns the base64-encoded string corresponding to the parameters of
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
          match selection |> Js.Optdef.to_option |> Option.map ipath_of_array with
          | None -> None
          | Some [] -> None
          | Some [ selection ] -> Some selection
          | Some _ ->
              js_log "Jsapi.lemmareqb : limited to one selection. Setting selection to None.";
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
        |> Fun.flip Marshal.to_string [] |> Base64.encode_string |> Js.string
      in
      !!doit ()

    (** Load the lemma database specified by the [data] object into the prover. *)
    method loadlemmas datab =
      (* Decode the data.
         The type annotation here is very important for unmarshaling to work. *)
      let (env, lemmas) : Api.Logic.lemmadb =
        datab |> Js.to_string |> Base64.decode_exn |> Fun.flip Marshal.from_string 0
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
        Proof.Lemmas.extend_env env @@ Proof.Lemmas.of_list
        @@ List.mapi (fun _ lemma -> (Handle.fresh (), lemma)) lemmas
      in
      (* Print debug info. *)
      js_log @@ Format.sprintf "Received lemmas (count=%d)\n" (List.length lemmas);
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
               let handle = handle |> Handle.toint |> string_of_int |> Js.string in
               let name = lemma.Proof.l_user |> Js.string in
               let form = Notation.f_tostring (Proof.Lemmas.env db) lemma.l_form |> Js.string in
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
      let selection = selection |> Js.Optdef.to_option |> Option.map ipath_of_array in
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
                Pred.or_ (Pred.link_sfl selection) (Pred.link_drewrite selection)
            | _ -> failwith "Jsapi.filterlemmas: only supports a single selection."
          end
      in
      (* Filter the lemma database. *)
      let proof = Utils.time "filter-lemmas" @@ fun () -> filter pred _self##.proof in
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

    (** [this#getduplicateb (hyp_handle : int)] gets the hypothesis in the current goal, 
        and returns the base64-encoded string of the corresponding ADuplicate action. *)
    method getduplicateb hyp_handle =
      let doit () =
        (* Get the hypothesis name. *)
        let hidmap = Proof.hidmap parent##.proof in
        let hyp_name = Hidmap.State.run (Hidmap.find hyp_handle) hidmap in
        (* Construct the ADuplicate action and encode it. *)
        Api.Logic.ADuplicate hyp_name |> Fun.flip Marshal.to_string [] |> Base64.encode_string
        |> Js.string
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
        Api.Logic.AClear hyp_name |> Fun.flip Marshal.to_string [] |> Base64.encode_string
        |> Js.string
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
        Api.Logic.AGeneralize hyp_name |> Fun.flip Marshal.to_string [] |> Base64.encode_string
        |> Js.string
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
        Api.Logic.ACut form |> Fun.flip Marshal.to_string [] |> Base64.encode_string |> Js.string
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
        Api.Logic.ALemma lemma.l_full |> Fun.flip Marshal.to_string [] |> Base64.encode_string
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
        hypothesis [from] before hypothesis [before]. 
        Both hypotheses must be part of this sub-goal. 
        Raises [InvalidHyphId] if [from] is not a hypothesis (for instance if it is a local variable). *)
    method movehyp from before =
      let doit () =
        (* First check that [from] is indeed a valid hypothesis handle. *)
        let subgoal = Proof.byid parent##.proof _self##.handle in
        let is_hypothesis = List.mem from (Proof.Hyps.ids subgoal.g_hyps) in
        if is_hypothesis
        then
          (* Actually move the hypothesis. *)
          Proof.Tactics.move parent##.proof ~goal_id:_self##.handle ~hyp_id:from
            ~dest_id:(Js.Opt.to_option before)
        else raise MoveOnlyHyps
      in
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

(** Print a single goal in Actema format (for debug purposes). *)
let print_goal (Proof.{ g_env; g_hyps; g_goal } : Proof.pregoal) : unit =
  (* Conclusion. *)
  let goal_html = Notation.f_tohtml ~id:None g_env g_goal in
  js_log @@ Format.asprintf "GOAL HTML :\n%a\n" (Tyxml.Xml.pp ()) goal_html
(*js_log @@ Format.sprintf "GOAL %s\n" (show_form g_goal);
  (* Hypotheses. *)
  List.iter
    begin
      fun (_handle, hyp) -> js_log @@ Format.sprintf "HYP %s\n" (show_form hyp.Proof.h_form)
    end
    (Proof.Hyps.to_list g_hyps);
  (* Environment. *)
  Map.iter
    begin
      fun name arity -> js_log @@ Format.sprintf "PRED %s ---> %s\n" name (show_arity arity)
    end
    g_env.env_prp;
  Map.iter
    begin
      fun name sig_ -> js_log @@ Format.sprintf "FUN %s ---> %s\n" name (show_sig_ sig_)
    end
    g_env.env_fun;
  Map.iter
    begin
      fun name name' -> js_log @@ Format.sprintf "SORT %s ---> %s\n" name name'
    end
    g_env.env_sort_name;
  Map.iter
    begin
      fun name ty_ ->
        js_log @@ Format.sprintf "TVAR %s ---> %s\n" name ([%derive.show: type_ option list] ty_)
    end
    g_env.env_tvar;
  Map.iter
    begin
      fun name ty_ ->
        js_log @@ Format.sprintf "EVAR %s ---> %s\n" name ([%derive.show: type_ list] ty_)
    end
    g_env.env_evar;
  Map.iter
    begin
      fun name bvars ->
        js_log @@ Format.sprintf "VAR %s ---> %s\n" name ([%derive.show: bvar list] bvars)
    end
    g_env.env_var*)

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
         (* Log the goals. *)
         List.iter print_goal gls;
         (* Create a new proof engine. *)
         js_proof_engine (!!(Proof.ginit hm) gls)
    end)

(* -------------------------------------------------------------------- *)
let () = export "engine"
