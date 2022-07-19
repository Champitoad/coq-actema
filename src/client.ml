open Lwt
open Cohttp
open Cohttp_lwt_unix

let addr = "http://127.0.0.1:8124"

let make_req (cmd : string) (param : string) =
  let body = Cohttp_lwt.Body.of_string param in
  let uri = Uri.of_string (addr ^ "/" ^ cmd) in
  Client.post ~body uri

exception ActemaError of string
exception UnsupportedRequestMethod of string
exception UnsupportedHttpResponseCode of int

let action (goal : Logic_t.goal) : Logic_t.atree t =
  (** Send request with goal *)

  let goalb =
    goal |>
    Logic_b.string_of_goal |>
    Base64.encode_string in
  let req = make_req "action" goalb in

  req >>= fun (resp, body) ->

  (** Receive response with action tree *)

  body |> Cohttp_lwt.Body.to_string >|= fun body ->

  let code = resp |> Response.status |> Code.code_of_status in
  match code with
  | 200 ->
      body |>
      Base64.decode_exn |>
      Logic_b.atree_of_string
  | 501 ->
      raise (UnsupportedRequestMethod body)
  | 550 ->
      raise (ActemaError body)
  | _ ->
      raise (UnsupportedHttpResponseCode code)
