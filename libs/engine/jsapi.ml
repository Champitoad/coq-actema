(* -------------------------------------------------------------------- *)
open Utils
open Proof

(* -------------------------------------------------------------------- *)
type source = Handle.t * [`C | `H of Handle.t]

(* -------------------------------------------------------------------- *)
exception InvalidASource

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
   *  - source (string) [only for the kind "dnd"]
   *    ID of th formula that received the dropped element
   *
   * An output action is an object with the following properties:
   *
   *  - description : the description of the action
   *  - highlight   : a JS array of IDs to highlight
   *  - action      : the related action (see [apply])
   *)
  method actions asource =
    let actions =
      let asource =
        match Js.to_string (Js.typeof asource) with
        | "string" ->
          `Click (Js.to_string asource)
        | "object" -> begin
          let asource = Js.Unsafe.coerce asource in
          match Js.as_string InvalidASource asource##.kind with
            | "click" ->
                `Click (Js.to_string asource##.path)
            | "dnd"   ->
                let source =
                  Js.as_string InvalidASource
                    asource##.source in
                let destination =
                  Js.as_string InvalidASource
                    asource##.destination in
                `DnD CoreLogic.{ source; destination; }
            | _ -> raise InvalidASource
          end
        | _ -> raise InvalidASource
      in CoreLogic.actions self##.proof asource
    in

    Js.array (
      Array.of_list
        (List.map (fun (p, ps, a) -> 
             let ps = Js.array (Array.of_list (List.map Js.string ps)) in

             Js.Unsafe.obj [|
               "description", Js.Unsafe.inject (Js.string p) ;
               "highlight"  , Js.Unsafe.inject ps            ;
               "action"     , Js.Unsafe.inject a             |]) actions))

  (* Same as [actions], but in async mode. TO BE TESTED *)
  method pactions path =
    let%lwt _ = Lwt.return () in Lwt.return (self##actions path)

  (* Apply the action [action] (as returned by [actions]) *)
  method apply action =
    js_proof_engine (CoreLogic.apply self##.proof action)
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
    let vars = Set.to_list (Fo.Prps.all goal.g_env) in
    Js.array (Array.of_list (List.map Js.string vars))

  (* Return all the local hypotheses (context) as a [js_hyps array] *)
  method context =
    let goal = Proof.byid parent##.proof self##.handle in
    let hyps = List.map (snd_map snd) (Map.bindings goal.g_hyps) in
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
    js_proof_engine (CoreLogic.intro ~variant (parent##.proof, handle))

  (* [this#elim (target : js_hyps)]] applies the relevant elimination
   * rule to the hypothesis [target] of the subgoal [this].
   *
   * Raise an exception if [target] does not belong to [this] *)
  method elim target =
    js_proof_engine (CoreLogic.elim target##.handle (parent##.proof, handle))

  (* [this#ivariants] Return the available introduction rules that can
   * be applied to the conclusion of [this] as a string array. The strings
   * are only for documentation purposes - only their position in the
   * returned array is meaningful and can be used as argument to [#intro]
   * to select the desired introduction rule. *)
  method ivariants =
    let aout = CoreLogic.ivariants (parent##.proof, handle) in
    let aout = Array.of_list (List.map Js.string aout) in
    Js.array aout

  method getmeta =
    Js.Opt.option (Proof.get_meta parent##.proof self##.handle)

  method setmeta meta =
    Proof.set_meta parent##.proof self##.handle (Js.Opt.to_option meta)
end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for a context hypothesis                                  *)
and js_hyps parent (i, (handle, hyp) : int * (Handle.t * Fo.form)) = object%js (self)
  (* back-link to the [js_subgoal] this hypothesis belongs to *)
  val parent = parent

  (* the handle (UID) of the hypothesis *)
  val handle = handle

  (* the handle position in its context *)
  val position = i

  (* the hypothesis as a [js_form] *)
  val form = js_form (parent##.handle, `H handle) hyp

  (* The enclosing proof engine *)
  val proof = parent##.parent

  method getmeta =
    Js.Opt.option (Proof.get_meta self##.proof##.proof self##.handle)

  method setmeta meta =
    Proof.set_meta self##.proof##.proof self##.handle (Js.Opt.to_option meta)
end

(* -------------------------------------------------------------------- *)
(* JS Wrapper for formulas                                              *)
and js_form (source : source) (form : Fo.form) :> < > Js.t = object%js
  (* Return the [mathml] of the formula *)  
  method mathml =
    let tag =
      match snd source with
      | `H _ -> "hypothesis"
      | `C   -> "conclusion"
    in
      Js.string
        (Format.asprintf "%a" (Tyxml.Xml.pp ())
        (Fo.Form.mathml ~tag:tag form))

  (* Return the [html] of the formula *)  
  method html =
    let prefix =
      match source with
      | h, `H i -> Format.sprintf "%d/%d" (Handle.toint h) (Handle.toint i)
      | h, `C   -> Format.sprintf "%d/0" (Handle.toint h)
    in
      Js.string
        (Format.asprintf "%a" (Tyxml.Xml.pp ())
        (Fo.Form.tohtml ~prefix form))

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
      let goal = Io.parse_goal (Io.from_string (Js.to_string x)) in
      let env, goal = Fo.Goal.check goal in
      js_proof_engine (Proof.init env goal)
  end)
