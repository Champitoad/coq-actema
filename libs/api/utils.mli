open Logic_t

val biniou_unhash_dict : int -> string option

val empty_env : env

module Uid : sig
  include Map.OrderedType
  val fresh : unit -> unit -> t
end with type t = uid

module LEnv : sig
  val exists : lenv -> vname -> bool
end

module Vars : sig
  val get : env -> vname -> bvar option
  val push : env -> name * bvar -> env
  val push_lenv : env -> lenv -> env
end

module Funs : sig
  val get : env -> name -> sig_ option
end

val t_equal : env -> type_ -> type_ -> bool

val einfer : env -> expr -> type_

val direct_subforms : form -> form list
val direct_subform : form -> int -> form

val string_of_expr : expr -> string
val string_of_form : form -> string
val string_of_goal : goal -> string
val string_of_proof : proof -> string

val get_hyp : goal -> uid -> hyp