open Cohttp
open Cohttp_lwt_unix
open Lwt.Syntax
open Api

exception ActemaError of string
exception UnsupportedRequestMethod of string
exception UnsupportedHttpResponseCode of int

(** The plugin sends the goals (in API format) to the frontend, 
    which sends back an action. *)
type action =
  | Do of int * Logic.action
  | Done
  | Undo
  | Redo
  | Lemmas of string option * Logic.term option

(** The IP address of the frontend (server). *)
let addr =
  let ip = try Unix.getenv "ACTEMAIP" with Not_found -> "localhost" in
  Printf.sprintf "http://%s:8124" ip

(** Make a single http POST request to the frontend. *)
let make_req (cmd : string) (param : string) =
  let body = Cohttp_lwt.Body.of_string param in
  let uri = Uri.of_string (addr ^ "/" ^ cmd) in
  Client.post ~body uri

(** Receive a [unit] action from the frontend. *)
let receive_unit (resp : Response.t) (_body : Cohttp_lwt.Body.t) : unit Lwt.t =
  let code = resp |> Response.status |> Code.code_of_status in
  match code with 200 -> Lwt.return () | _ -> raise (UnsupportedHttpResponseCode code)

(** Receive an [action] response from the frontend. *)
let receive_action (resp : Response.t) (body : Cohttp_lwt.Body.t) : action Lwt.t =
  let* body = body |> Cohttp_lwt.Body.to_string in
  let code = resp |> Response.status |> Code.code_of_status in
  match code with
  | 200 -> begin
      (* The frontend gave a proof action. *)
      match String.split_on_char '\n' body with
      | [ subgoal_idx; actionb ] ->
          let idx = int_of_string subgoal_idx in
          let action : Logic.action =
            actionb |> Base64.decode_exn |> Fun.flip Marshal.from_string 0
          in
          Lwt.return @@ Do (idx, action)
      | _ -> failwith "Unexpected response body for 'action' request"
    end
  | 251 -> Lwt.return Done
  | 252 -> Lwt.return Undo
  | 253 -> Lwt.return Redo
  | 254 ->
      (* The frontend requested a list of lemmas. *)
      let (pattern, selection) : string option * Logic.term option =
        body |> Base64.decode_exn |> Fun.flip Marshal.from_string 0
      in
      Lwt.return @@ Lemmas (pattern, selection)
  | 501 -> raise (UnsupportedRequestMethod body)
  | 550 -> raise (ActemaError body)
  | _ -> raise (UnsupportedHttpResponseCode code)

let send_lemmas (lemmas : Logic.lemma list) (env : Logic.env) : action Lwt.t =
  (* Send request with lemmas and environment. *)
  let datab = (env, lemmas) |> Fun.flip Marshal.to_string [] |> Base64.encode_string in
  let* resp, body = make_req "lemmas" datab in
  (* Handle the response. *)
  receive_action resp body

let send_goals (goals : Logic.goals) : action Lwt.t =
  (* Send request with goals. *)
  let goalsb = goals |> Fun.flip Marshal.to_string [] |> Base64.encode_string in
  let req = make_req "action" goalsb in
  (* Receive response with action. *)
  let* resp, body = req in
  receive_action resp body

let send_qed () : unit Lwt.t =
  let req = make_req "qed" "" in
  let* resp, body = req in
  receive_unit resp body

let send_error (msg : string) : unit Lwt.t =
  let req = make_req "error" msg in
  let* resp, body = req in
  receive_unit resp body
