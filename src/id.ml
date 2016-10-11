type t = Id of int

let string_of_id (Id x) =
  Printf.sprintf "[%d]" x
