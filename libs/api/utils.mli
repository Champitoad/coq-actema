open Logic_t

val biniou_unhash_dict : int -> string option

val empty_env : env

module Uid : sig
  include Map.OrderedType
  val fresh : unit -> unit -> t
end with type t = uid

module Vars : sig
  val push : env -> name * bvar -> env
end

val string_of_expr : expr -> string
val string_of_form : form -> string
val string_of_goal : goal -> string
val string_of_proof : proof -> string

val get_hyp : goal -> uid -> hyp