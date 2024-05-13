open Api_new
open Lang

let () =
  let a = Name.make "a" in
  let x = Term.Var (Name.make "xxx") in
  let y = Term.Var (Name.make "y") in
  let f = Term.Cst (Name.make "f_long") in
  let t =
    Term.Prod
      ( a
      , Term.mkApps f [ Term.mkApp f x; Term.mkApps f [ x; y ] ]
      , Term.Lambda (Name.make "a", x, Var a) )
  in
  Format.printf "%a\n" (Tyxml.Xml.pp ())
    (Notation.term_to_xml ~width:15 Env.empty t)
