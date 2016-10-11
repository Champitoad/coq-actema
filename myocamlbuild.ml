(* -------------------------------------------------------------------- *)
open Ocamlbuild_plugin

let mydispatch = function
   | After_rules ->
       (* Numerical warnings *)
       begin
         let wflag error mode wid =
           let mode = match mode with
             | `Enable  -> "+"
             | `Disable -> "-"
             | `Mark    -> "@"
           in
             match error with
             | false -> S[A"-w"; A(Printf.sprintf "%s%d" mode wid)]
             | true  -> S[A"-warn-error"; A(Printf.sprintf "%s%d" mode wid)]
         in
           for i = 1 to 45 do
             flag ["ocaml"; "compile"; Printf.sprintf "warn_+%d" i] & (wflag false `Enable  i);
             flag ["ocaml"; "compile"; Printf.sprintf "warn_-%d" i] & (wflag false `Disable i);
             flag ["ocaml"; "compile"; Printf.sprintf "warn_@%d" i] & (wflag false `Mark    i);
             flag ["ocaml"; "compile"; Printf.sprintf "werr_+%d" i] & (wflag true  `Enable  i);
             flag ["ocaml"; "compile"; Printf.sprintf "werr_-%d" i] & (wflag true  `Disable i);
             flag ["ocaml"; "compile"; Printf.sprintf "werr_@%d" i] & (wflag true  `Mark    i)
           done
       end

   | _ -> ()

(* -------------------------------------------------------------------- *)
let hooks = [mydispatch; Ocamlbuild_js_of_ocaml.dispatcher]

let () =
  Ocamlbuild_plugin.dispatch
    (fun hook -> List.iter (fun cb -> cb hook) hooks)
