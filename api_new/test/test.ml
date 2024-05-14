open Api_new
open Lang

let () =
  let a = Name.make "a" in
  let x = Term.mkVar @@ Name.make "xxx" in
  let y = Term.mkVar @@ Name.make "y" in
  let f = Term.mkCst @@ Name.make "f_long" in
  let t =
    Term.mkProd a
      (Term.mkApps f [ Term.mkApp f x; Term.mkApps f [ x; y ] ])
      (Term.mkLambda a x @@ Term.mkVar a)
  in
  Format.printf "%a\n" (Tyxml.Xml.pp ())
    (Notation.term_to_xml ~width:15 Env.empty t)
