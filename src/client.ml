open Lwt
open Cohttp
open Cohttp_lwt_unix

let addr = "http://127.0.0.1:8124"

let make_req (cmd : string) (param : string) =
  let body = Cohttp_lwt.Body.of_string param in
  let uri = Uri.of_string (addr ^ "/" ^ cmd) in
  Client.post ~body uri

let action (goal : Logic_t.goal) : Logic_t.atree t =
  (** Send request with goal *)

  let goalb =
    goal |>
    Logic_b.string_of_goal |>
    Base64.encode_string in
  let req = make_req "action" goalb in

  req >>= fun (resp, body) ->

  (** Receive response with action tree *)

  (* let code = resp |> Response.status |> Code.code_of_status in
  Printf.printf "Response code: %d\n" code;
  Printf.printf "Headers: %s\n" (resp |> Response.headers |> Header.to_string); *)

  body |> Cohttp_lwt.Body.to_string >|= fun proofb ->
  (* Printf.printf "Body of length: %d\n" (String.length body); *)
  
  proofb |>
  Base64.decode_exn |>
  Logic_b.atree_of_string