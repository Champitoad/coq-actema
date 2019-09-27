(* -------------------------------------------------------------------- *)
type reader

(* -------------------------------------------------------------------- *)
val from_channel : name:string -> in_channel -> reader
val from_file    : string -> reader
val from_string  : string -> reader
val finalize     : reader -> unit

(* -------------------------------------------------------------------- *)
val parse_form : reader -> Syntax.pform
val parse_goal : reader -> Syntax.pgoal
