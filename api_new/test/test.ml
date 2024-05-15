open Api_new
open Lang

let () =
  let term =
    QCheck2.Gen.generate1 @@ TermGen.typed ~closed:true Env.test_env Term.mkProp
  in
  let ty = Typing.check Env.test_env term in
  Format.printf "%s\n\n%s\n"
    (Notation.term_to_string Env.test_env term)
    (Notation.term_to_string Env.test_env ty)

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
