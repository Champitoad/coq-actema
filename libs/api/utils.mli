open Logic_t

val empty_env : env

val biniou_unhash_dict : int -> string option
val string_of_goal : goal -> string
val string_of_proof : proof -> string

val get_hyp : goal -> uid -> hyp