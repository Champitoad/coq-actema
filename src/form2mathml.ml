(* -------------------------------------------------------------------- *)
module E = Engine

open Engine.Utils

(* -------------------------------------------------------------------- *)
let main () =
  let reader = E.Io.from_channel ~name:"<stdin>" stdin in
  let pst    = E.Io.parse_form reader in
  let ast    = E.Fo.Form.check E.Fo.Env.empty pst in
  let txt    = E.Fo.Form.tostring ast in

  Format.printf "%s@." txt

(* -------------------------------------------------------------------- *)
let () = main ()
