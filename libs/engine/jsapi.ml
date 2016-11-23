(* -------------------------------------------------------------------- *)
module Api : sig
  val parse_form : string -> string
end = struct
  let parse_form (s : string) =
    let f = Io.parse_form (Io.from_string s) in
    let f = Fo.Form.mathml (Fo.Form.check f) in
    let b = Buffer.create 128 in
    Format.fprintf (Format.formatter_of_buffer b)
      "%a%!" (Tyxml.Xml.pp ()) f;
    Buffer.contents b
end

let export (name : string) : unit =
  Js.export name (object%js
    method parse x = x |>
      Js.to_string |> Api.parse_form |> Js.string
  end)
