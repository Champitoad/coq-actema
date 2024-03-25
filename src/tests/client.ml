open Lwt
open Cohttp
open Cohttp_lwt_unix

let addr = "http://127.0.0.1:8124"

let make_req (cmd : string) (params : (string * string) list) =
  let params =
    params |>
    List.map (fun (k, v) -> k ^ "=" ^ v) |>
    String.concat "&" in
  let uri = Uri.of_string (addr ^ "/" ^ cmd ^ "?" ^ params) in
  Client.post uri

let body =
  let req = make_req "action" [("goal", "A; |- A -> A")] in
  req >>= fun (resp, body) ->

  let code = resp |> Response.status |> Code.code_of_status in
  Printf.printf "Response code: %d\n" code;
  Printf.printf "Headers: %s\n" (resp |> Response.headers |> Header.to_string);

  body |> Cohttp_lwt.Body.to_string >|= fun body ->
  Printf.printf "Body of length: %d\n" (String.length body);
  body

let () =
  let body = Lwt_main.run body in
  print_endline ("Received body\n" ^ body)