open Api
  open Fo
  open Fo.Translate
  open Proof
  open Hidmap
  open State
  open CoreLogic

  exception UnsupportedAction of action_type

  let of_ctxt (ctxt : ctxt) : Logic_t.ctxt State.t =
    let* uid =
      match ctxt.kind with
      | `Concl -> return "concl"
      | `Hyp | `Var _ -> find (Handle.ofint ctxt.handle)
    in
    return Logic_t.{ kind = ctxt.kind; handle = uid }

  let of_ipath (p : ipath) : Logic_t.ipath State.t =
    let* ctxt = of_ctxt p.ctxt in
    return Logic_t.{ ctxt; sub = p.sub }

  let of_lenv (lenv : LEnv.lenv) : Fo_t.lenv =
    LEnv.bindings lenv |> List.map (fun (x, ty) -> (x, of_type_ ty))

  let of_itrace (itrace : itrace) : Logic_t.itrace =
    List.map
      begin
        fun (i, w) -> (i, Option.map (fun (le1, le2, e) -> (of_lenv le1, of_lenv le2, of_expr e)) w)
      end
      itrace

  let of_action (proof : Proof.proof) ((hd, a) : action) : Logic_t.action State.t =
    match a with
    | `Intro variant -> return (`AIntro (variant, None))
    | `Elim (subhd, i) ->
        let goal = Proof.byid proof hd in
        let hyp = (Proof.Hyps.byid goal.g_hyps subhd).h_form in
        let exact = Form.f_equal goal.g_env hyp goal.g_goal in
        let* uid = find subhd in
        return (if exact then `AExact uid else `AElim (uid, i))
    | `Lemma name -> return (`ALemma name)
    | `Ind subhd ->
        let* uid = find subhd in
        return (`AInd uid)
    | `Simpl tgt ->
        let* tgt = of_ipath tgt in
        return (`ASimpl tgt)
    | `Red tgt ->
        let* tgt = of_ipath tgt in
        return (`ARed tgt)
    | `Indt tgt ->
        let* tgt = of_ipath tgt in
        return (`AIndt tgt)
    | `Case tgt ->
        let* tgt = of_ipath tgt in
        return (`ACase tgt)
    | `Pbp tgt ->
        let* tgt = of_ipath tgt in
        return (`APbp tgt)
    | `Hyperlink (lnk, actions) -> begin
        match (lnk, actions) with
        | ([ src ], [ dst ]), [ `Subform substs ] ->
            let _, itrace = dlink (src, dst) substs proof in
            let* src = of_ipath src in
            let* dst = of_ipath dst in
            return (`ALink (src, dst, of_itrace itrace))
        | _, [ `Instantiate (wit, tgt) ] ->
            let* tgt = of_ipath tgt in
            return (`AInstantiate (of_expr wit, tgt))
        | _, _ :: _ :: _ -> failwith "Cannot handle multiple link actions yet"
        | _, _ -> raise (UnsupportedAction a)
      end
    | _ -> raise (UnsupportedAction a)

  let export_action hm proof a = run (of_action proof a) hm
