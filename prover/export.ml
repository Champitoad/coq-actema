open Utils.Pervasive
open Api

exception UnsupportedAction of Actions.preaction

let export_action proof goal_id preaction : Logic.action =
  match (preaction : Actions.preaction) with
  | Exact hyp_name -> Logic.AExact hyp_name
  | Intro side -> Logic.AIntro side
  | Elim (hyp_name, i) -> Logic.AElim (hyp_name, i)
  | Hyperlink (hyperlink, linkactions) -> begin
      match (hyperlink, linkactions) with
      | ([ src ], [ dst ]), [ Subform subst ] ->
          (* This is where we perform deep interaction. *)
          let itrace = Interact.dlink (src, dst) subst proof in
          Logic.ALink (src, dst, itrace)
      | _ -> raise @@ UnsupportedAction preaction
    end
  (*| `Lemma name -> return (Logic.ALemma name)
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
      end*)
  | _ -> raise @@ UnsupportedAction preaction
