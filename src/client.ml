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

let qed () : unit t =
  let req = make_req "qed" "" in

  req >>= fun (resp, _) ->

  let code = resp |> Response.status |> Code.code_of_status in
  match code with
  | 200 ->
      return ()
  | _ ->
      raise (UnsupportedHttpResponseCode code)

let action (goal : Logic_t.goal) : (int * Logic_t.action) option t =
  (* Send request with goal *)

  let goalb =
    goal |>
    Logic_b.string_of_goal |>
    Base64.encode_string in
  let req = make_req "action" goalb in

  req >>= fun (resp, body) ->

  (* Receive response with proof *)

  body |> Cohttp_lwt.Body.to_string >|= fun body ->

  let code = resp |> Response.status |> Code.code_of_status in
  match code with
  | 200 ->
      body |>
      String.split_on_char '\n' |>
      begin function
      | [subgoal_idx; actionb] ->
          let idx = int_of_string subgoal_idx in
          let action =
            actionb |>
            Base64.decode_exn |>
            Logic_b.action_of_string in
          Some (idx, action)
      | _ ->
          failwith "Unexpected response body for 'action' request"
      end
  | 201 ->
      None
  | 501 ->
      raise (UnsupportedRequestMethod body)
  | 550 ->
      raise (ActemaError body)
  | _ ->
      raise (UnsupportedHttpResponseCode code)
