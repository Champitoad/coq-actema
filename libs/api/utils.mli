open Logic_t

val biniou_unhash_dict : int -> string option

val empty_env : env

module Uid : sig
  include Map.OrderedType
  val fresh : unit -> unit -> t
end with type t = uid

module LEnv : sig
  val exists : lenv -> vname -> bool
  val enter : lenv -> name -> type_ -> lenv
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

exception TypingError

val einfer : env -> expr -> type_

val form_of_term : term -> form
val expr_of_term : term -> expr

exception InvalidPath of ipath
exception InvalidSubFormPath of int list
exception InvalidSubExprPath of int list

val direct_subforms : form -> form list
val direct_subform : form -> int -> form
val subform : form -> int list -> form
val direct_subexprs : expr -> expr list
val direct_subexpr : expr -> int -> expr
val subexpr : expr -> int list -> expr
val direct_subterms : term -> term list
val direct_subterm : term -> int -> term
val subterm : term -> int list -> term

type pol = Pos | Neg | Sup

val term_of_ipath : goal -> ipath -> term
val pol_of_ipath : goal -> ipath -> pol

val string_of_expr : expr -> string
val string_of_form : form -> string
val string_of_term : term -> string
val string_of_goal : goal -> string
val string_of_goals : goals -> string
val string_of_itrace : itrace -> string
val string_of_action : action -> string
val string_of_proof : proof -> string

val get_hyp : goal -> uid -> hyp