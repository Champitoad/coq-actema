open Api
open Lang

let () =
  (* Term. *)
  let g = Name.make "x" in
  let term = Term.(mkProd g (mkCst (Name.make "nat")) (mkVar 0)) in
  Format.printf "TERM\n%s\n" (Notation.term_to_string Env.test_env term);
  (* Type. *)
  try
    let ty = Typing.check Env.test_env term in
    Format.printf "TYPE\n%s\n" (Notation.term_to_string Env.test_env ty)
  with Typing.TypingError err ->
    Format.printf "ERR\n%a\n" Typing.pp_typeError err
