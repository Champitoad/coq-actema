(* -------------------------------------------------------------------- *)
module Api : sig
  val parse_form : string -> string
end = struct
  let parse_form (x : string) =
    let (_ : Syntax.pform) = Io.parse_form (Io.from_string x) in
    "OK"
end

let export (name : string) : unit =
  Js.export name (object%js
    method parse x = x |>
      Js.to_string |> Api.parse_form |> Js.string
  end)
