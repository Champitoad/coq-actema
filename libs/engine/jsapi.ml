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
let rec js_proof_engine (proof : Proof.proof) = object%js (self)
  val proof  = proof
  val handle = Handle.fresh ()

  (* Return a [js_subgoal] array of all the opened subgoals *)
  method subgoals =
    let subgoals = Proof.opened proof in
    let subgoals = List.map (js_subgoal self) subgoals in
    Js.array (Array.of_list subgoals)

  (* Return true when there are no opened subgoals left *)
  method closed =
    Js.bool (Proof.closed proof)

  (* Get the meta-data attached to this proof engine *)
  method getmeta =
    Js.Opt.option (Proof.get_meta proof self##.handle)

  (* Attach meta-data to the proof engine *)
  method setmeta meta =
    Proof.set_meta proof self##.handle (Js.Opt.to_option meta)

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
   *    ID of the "clicked" formula / sub-formula
   *
   *  - source (string) [only for the kind "dnd"]
   *    ID of the formula that is being dropped
   *
   *  - destination (string) [only for the kind "dnd"]
   *    ID of th formula that received the dropped element
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
      let asource =
        match Js.to_string (Js.typeof asource) with
        | "string" ->
          [`Click (`S (Js.to_string asource))]
        | "object" -> begin
          let asource = Js.Unsafe.coerce asource in
          match Js.as_string InvalidASource asource##.kind with
            | "click" ->
                [`Click (`S (Js.to_string asource##.path))]
            | "dnd" ->
                let source =
                  `S (Js.as_string InvalidASource asource##.source) in
                let destination =
                  Option.map
                    (fun x -> `S (Js.as_string InvalidASource x))
                    (Js.Opt.to_option asource##.destination) in
                [`DnD CoreLogic.{ source; destination; }]
            | "any" ->
                let path = `S (Js.to_string asource##.path) in
                [`Click path; `DnD CoreLogic.{ source = path; destination = None; }]
            | _ -> raise InvalidASource
          end
        | _ -> raise InvalidASource
      in List.flatten
           (List.map (!!(CoreLogic.actions self##.proof)) asource)
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
    let%lwt _ = Lwt.return () in Lwt.return (self##actions path)

  (* Apply the action [action] (as returned by [actions]) *)
  method apply action =
    js_proof_engine (!! (uc CoreLogic.apply) (self##.proof, action))

  (* Cut rule *)
  method cut form handle =
    let doit () =
      let goal = Proof.byid self##.proof (Handle.ofint handle) in
      let form = Io.parse_form (Io.from_string (Js.to_string form)) in
      let form = Fo.Form.check goal.g_env form in
      CoreLogic.cut form (self##.proof, Handle.ofint handle)
    in js_proof_engine (!!doit ())
end

(* -------------------------------------------------------------------- *)
(* JS wrapper for subgoals                                              *)
and js_subgoal parent (handle : Handle.t) = object%js (self)
  (* back-link to the [js_proof_engine] this subgoal belongs to *)
  val parent = parent

  (* the handle (UID) of the subgoal *)
  val handle = handle

  (* Return all the propositional variables as a [string array] *)
  method vars =
    let goal = Proof.byid parent##.proof self##.handle in
    let vars = List.fst (Map.bindings (Fo.Prps.all goal.g_env)) in
    Js.array (Array.of_list (List.map Js.string vars))

  (* Return all the local hypotheses (context) as a [js_hyps array] *)
  method context =
    let goal = Proof.byid parent##.proof self##.handle in
    let hyps = Map.bindings goal.g_hyps in
    let hyps =
      let key  = fun ((i, _) : Handle.t * Proof.hyp) -> Handle.toint i in
      let deps = fun ((_, x) : Handle.t * Proof.hyp) ->
        List.of_option (Option.map Handle.toint x.h_src) in

      try  List.rev (List.topo key deps hyps)
      with List.TopoFailure -> hyps
    in

    Js.array (Array.of_list (List.mapi (fun i x -> js_hyps self (i, x)) hyps))

  (* Return the subgoal conclusion as a [js_form] *)
  method conclusion =
    let goal  = Proof.byid parent##.proof self##.handle in
    js_form (self##.handle, `C) goal.g_goal

  (* [this#intro [variant : int]] applies the relevant introduction
   * rule to the conclusion of the subgoal [this]. The parameter
   * [variant] gives the variant of the introduction rule to be applied.
   *
   * See [#ivariants] *)

  method intro variant =
    js_proof_engine (!!(CoreLogic.intro ~variant) (parent##.proof, handle))

  (* [this#elim (target : js_hyps)]] applies the relevant elimination
   * rule to the hypothesis [target] of the subgoal [this].
   *
   * Raise an exception if [target] does not belong to [this] *)
  method elim target =
    let data = (target##.handle, (parent##.proof, handle)) in
    js_proof_engine (!!(uc CoreLogic.elim) data)

  (* [this#ivariants] Return the available introduction rules that can
   * be applied to the conclusion of [this] as a string array. The strings
   * are only for documentation purposes - only their position in the
   * returned array is meaningful and can be used as argument to [#intro]
   * to select the desired introduction rule. *)
  method ivariants =
    let aout = !!CoreLogic.ivariants (parent##.proof, handle) in
    let aout = Array.of_list (List.map Js.string aout) in
    Js.array aout

  method getmeta =
    Js.Opt.option (Proof.get_meta parent##.proof self##.handle)

  method setmeta meta =
    Proof.set_meta parent##.proof self##.handle (Js.Opt.to_option meta)
end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for a context hypothesis                                  *)
and js_hyps parent (i, (handle, hyp) : int * (Handle.t * Proof.hyp)) =
object%js (self)
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

  method getmeta =
    Js.Opt.option (Proof.get_meta self##.proof##.proof self##.handle)

  method setmeta meta =
    Proof.set_meta self##.proof##.proof self##.handle (Js.Opt.to_option meta)
end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for formulas                                              *)
and js_form (source : source) (form : Fo.form) :> < > Js.t = object%js (self)
  (* Return the [html] of the formula *)  
  method html =
    self##htmltag true

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
        (Fo.Form.tohtml ?id:prefix form))

  (* Return an UTF8 string representation of the formula *)
  method tostring =
    Js.string (Fo.Form.tostring form)
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
        let goal = Io.parse_goal (Io.from_string (Js.to_string x)) in
        Fo.Goal.check goal
      ) () in js_proof_engine (Proof.init env goal)
  end)
