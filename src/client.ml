open Lwt
open Cohttp
open Cohttp_lwt_unix


let addr =
  let ip =
    try Unix.getenv "ACTEMAIP"
    with Not_found -> "localhost" in
  Printf.sprintf "http://%s:8124" ip

let make_req (cmd : string) (param : string) =
  let body = Cohttp_lwt.Body.of_string param in
  let uri = Uri.of_string (addr ^ "/" ^ cmd) in
  Client.post ~body uri

exception ActemaError of string
exception UnsupportedRequestMethod of string
exception UnsupportedHttpResponseCode of int

type action =
| Do of int * Logic_t.action
| Done | Undo | Redo


(** Send a set of lemmas to the frontend, and wait for an (empty) response. *)
let send_lemmas (lemmas : Logic_t.lemmas) : unit t = 
  let open Lwt.Syntax in
  (* Send request with lemmas. *)
  let lemmasb = lemmas
              |> Logic_b.string_of_lemmas 
              |> Base64.encode_string in
  let* (resp, body) = make_req "lemmas" lemmasb in

  (* Handle the response. *)
  let code = resp |> Response.status |> Code.code_of_status in
  match code with   
    | 200 -> return ()
    | _   -> raise (UnsupportedHttpResponseCode code)


(** Send the goals to the frontend, and receive an action as response. *)
let action (goals : Logic_t.goals) : action t =
  (* Send request with goals *)

  let goalsb = goals |>
    Logic_b.string_of_goals |>
    Base64.encode_string in
  let req = make_req "action" goalsb in

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
          Do (idx, action)
      | _ ->
          failwith "Unexpected response body for 'action' request"
      end
  | 201 -> Done
  | 202 -> Undo
  | 203 -> Redo
  | 501 ->
      raise (UnsupportedRequestMethod body)
  | 550 ->
      raise (ActemaError body)
  | _ ->
      raise (UnsupportedHttpResponseCode code)

let qed () : unit t =
  let req = make_req "qed" "" in
  req >>= fun (resp, _) ->
  let code = resp |> Response.status |> Code.code_of_status in
  match code with
  | 200 ->
      return ()
  | _ ->
      raise (UnsupportedHttpResponseCode code)

let error (msg : string) : unit t =
  let req = make_req "error" msg in
  req >>= fun (resp, _) ->
  let code = resp |> Response.status |> Code.code_of_status in
  match code with
  | 200 ->
      return ()
  | _ ->
      raise (UnsupportedHttpResponseCode code)