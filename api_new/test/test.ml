open Api_new
open Lang

let () =
  (* Env. *)
  let or_ = Name.make "or" in
  let not_ = Name.make "not" in
  let nat = Name.make "nat" in
  let le = Name.make "le" in
  let env =
    Env.empty
    |> Env.add_constant or_ Term.(mkArrows [ mkProp; mkProp; mkProp ])
    |> Env.add_constant not_ Term.(mkArrow mkProp mkProp)
    |> Env.add_constant nat Term.mkType
    |> Env.add_constant le Term.(mkArrows [ mkCst nat; mkCst nat; mkProp ])
  in

  let term = QCheck2.Gen.generate1 @@ TermGen.scoped env in
  Format.printf "%s\n" @@ Notation.term_to_string env term

(* Term. *)
(*let a = Name.make "a" in
  let b = Name.make "b" in
  let t =
    Term.(
      mkLambda a (mkCst nat)
      @@ mkLambda a (mkArrow (mkCst nat) (mkCst nat))
      @@ mkProd a (mkCst nat)
      @@ mkProd b (mkCst nat)
      @@ mkApps (mkCst or_)
           [ mkApps (mkCst le) [ mkVar a; mkVar b ]
           ; mkApps (mkCst le) [ mkVar b; mkVar a ]
           ])
  in
  (* Print. *)
  try
    let ty = Typing.check env t in
    Format.printf "%s\n" (Notation.term_to_string env ty)
  with Typing.TypingError err -> Format.printf "%a\n" Typing.pp_typeError err
*)
