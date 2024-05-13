open Api_new
open Lang

let () =
  let x = Term.Var (Name.make "xxx") in
  let y = Term.Var (Name.make "y") in
  let f = Term.Cst (Name.make "f_long") in
  let t =
    Term.Prod
      ( Name.make "a"
      , Term.mkApps f [ Term.mkApp f x; Term.mkApps f [ x; y ] ]
      , x )
  in
  Format.printf "%s\n" (Notation.term_to_string ~width:15 Env.empty t)
