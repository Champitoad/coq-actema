(* -------------------------------------------------------------------- *)
open Utils
open Proof

(* -------------------------------------------------------------------- *)
module Js = Js_of_ocaml.Js

(* -------------------------------------------------------------------- *)
type source = Handle.t * [`C | `H of int]

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

  method getmeta =
    Js.Opt.option (Proof.get_meta proof self##.handle)

  method setmeta meta =
    Proof.set_meta proof self##.handle (Js.Opt.to_option meta)
end

(* -------------------------------------------------------------------- *)
(* JS wrapper for subgoals                                              *)
and js_subgoal parent (handle : Handle.t) = object%js (self)
  (* back-ling to the [js_proof_engine] this subgoal belongs to *)
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
    js_form (self##.parent##.handle, `C) goal.g_goal

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
  val form = js_form (parent##.parent##.handle, `H i) hyp

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
      | h, `H i -> Format.sprintf "%d/%d" (Handle.toint h) (i+1)
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
