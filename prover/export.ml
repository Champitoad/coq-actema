open Utils
open Fo
open Fo.Translate
open Proof
open Hidmap
open State
open CoreLogic
open Interact
open Api

exception UnsupportedAction of Actions.action_type

let of_ctxt (ctxt : IPath.ctxt) : Logic.ctxt State.t =
  let* handle =
    match ctxt.kind with
    | `Concl -> return "concl"
    | `Hyp | `Var _ -> find (Handle.ofint ctxt.handle)
  in
  let kind =
    match ctxt.kind with
    | `Hyp -> Logic.Hyp
    | `Concl -> Logic.Concl
    | `Var `Head -> Logic.Var Logic.Head
    | `Var `Body -> Logic.Var Logic.Body
  in
  return Logic.{ kind; handle }

let of_ipath (p : IPath.t) : Logic.ipath State.t =
  let* ctxt = of_ctxt p.ctxt in
  return Logic.{ ctxt; sub = p.sub }

let of_lenv (lenv : LEnv.lenv) : Logic.lenv =
  LEnv.bindings lenv |> List.map (fun (x, ty) -> (x, of_type_ ty))

let of_itrace (itrace : itrace) : Logic.itrace =
  List.map
    begin
      fun (i, w) ->
        ( i
        , Option.map
            (fun (le1, le2, e) -> (of_lenv le1, of_lenv le2, of_expr e))
            w )
    end
    itrace

let of_action (proof : Proof.proof) ((hd, a) : Handle.t * Actions.action_type) :
    Logic.action State.t =
  match a with
  | `Intro side -> return (Logic.AIntro side)
  | `Elim (subhd, i) ->
      let goal = Proof.byid proof hd in
      let hyp = (Proof.Hyps.byid goal.g_hyps subhd).h_form in
      let exact = Form.f_equal goal.g_env hyp goal.g_goal in
      let* uid = find subhd in
      return (if exact then Logic.AExact uid else Logic.AElim (uid, i))
  | `Lemma name -> return (Logic.ALemma name)
  | `Ind subhd ->
      js_log @@ Format.sprintf "Export.of_action `Ind %d\n" (Handle.toint subhd);
      let* state = State.get in
      HandleMap.iter
        (fun handle name ->
          js_log @@ Format.sprintf "%d --> %s\n" (Handle.toint handle) name)
        state;
      let* uid = find subhd in
      js_log @@ Format.sprintf "Found: %s\n" uid;
      return (Logic.AInd uid)
  | `Simpl tgt ->
      let* tgt = of_ipath tgt in
      return (Logic.ASimpl tgt)
  | `Red tgt ->
      let* tgt = of_ipath tgt in
      return (Logic.ARed tgt)
  | `Indt tgt ->
      let* tgt = of_ipath tgt in
      return (Logic.AIndt tgt)
  | `Case tgt ->
      let* tgt = of_ipath tgt in
      return (Logic.ACase tgt)
  | `Pbp tgt ->
      let* tgt = of_ipath tgt in
      return (Logic.APbp tgt)
  | `Hyperlink (lnk, actions) -> begin
      match (lnk, actions) with
      | ([ src ], [ dst ]), [ `Subform substs ] ->
          let itrace = dlink (src, dst) substs proof in
          let* src = of_ipath src in
          let* dst = of_ipath dst in
          return (Logic.ALink (src, dst, of_itrace itrace))
      | _, [ `Instantiate (wit, tgt) ] ->
          let* tgt = of_ipath tgt in
          return (Logic.AInstantiate (of_expr wit, tgt))
      | _, _ :: _ :: _ -> failwith "Cannot handle multiple link actions yet"
      | _, _ -> raise @@ UnsupportedAction a
    end
  | _ -> raise @@ UnsupportedAction a

let export_action hm proof a = run (of_action proof a) hm
