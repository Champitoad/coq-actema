open QCheck
open Api.Fo_t

let return = Gen.return
let ( let* ) = Gen.bind

(*let choose xs =
  if Array.length xs = 0 then failwith "choose : empty list"
  else
    let idx = Random.int (Array.length xs) in
    xs.(idx)*)

let gen_type : type_ Gen.t = return $ `TVar
