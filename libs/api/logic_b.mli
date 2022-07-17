(* Auto-generated from "logic.atd" *)
[@@@ocaml.warning "-27-32-33-35-39"]

type bkind = Logic_t.bkind

type logcon = Logic_t.logcon

type name = Logic_t.name

type pkind = Logic_t.pkind

type uid = Logic_t.uid

type ctxt = Logic_t.ctxt = { kind: pkind; handle: uid }

type ipath = Logic_t.ipath = { root: uid; ctxt: ctxt; sub: int list }

type vname = Logic_t.vname

type type_ = Logic_t.type_

type expr = Logic_t.expr

type form = Logic_t.form

type choice = Logic_t.choice

type itrace = Logic_t.itrace

type action = Logic_t.action

type atree = Logic_t.atree

type term = Logic_t.term

type arity = Logic_t.arity

type sig_ = Logic_t.sig_

type bvar = Logic_t.bvar

type env = Logic_t.env = {
  env_prp: (name * arity) list;
  env_fun: (name * sig_) list;
  env_var: (name * bvar list) list;
  env_tvar: (name * type_ option list) list;
  env_handles: (vname * uid) list
}

type goal = Logic_t.goal

(* Writers for type bkind *)

val bkind_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!bkind}.
      Readers may support more than just this tag. *)

val write_untagged_bkind :
  Bi_outbuf.t -> bkind -> unit
  (** Output an untagged biniou value of type {!type:bkind}. *)

val write_bkind :
  Bi_outbuf.t -> bkind -> unit
  (** Output a biniou value of type {!type:bkind}. *)

val string_of_bkind :
  ?len:int -> bkind -> string
  (** Serialize a value of type {!type:bkind} into
      a biniou string. *)

(* Readers for type bkind *)

val get_bkind_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> bkind)
  (** Return a function that reads an untagged
      biniou value of type {!type:bkind}. *)

val read_bkind :
  Bi_inbuf.t -> bkind
  (** Input a tagged biniou value of type {!type:bkind}. *)

val bkind_of_string :
  ?pos:int -> string -> bkind
  (** Deserialize a biniou value of type {!type:bkind}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type logcon *)

val logcon_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!logcon}.
      Readers may support more than just this tag. *)

val write_untagged_logcon :
  Bi_outbuf.t -> logcon -> unit
  (** Output an untagged biniou value of type {!type:logcon}. *)

val write_logcon :
  Bi_outbuf.t -> logcon -> unit
  (** Output a biniou value of type {!type:logcon}. *)

val string_of_logcon :
  ?len:int -> logcon -> string
  (** Serialize a value of type {!type:logcon} into
      a biniou string. *)

(* Readers for type logcon *)

val get_logcon_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> logcon)
  (** Return a function that reads an untagged
      biniou value of type {!type:logcon}. *)

val read_logcon :
  Bi_inbuf.t -> logcon
  (** Input a tagged biniou value of type {!type:logcon}. *)

val logcon_of_string :
  ?pos:int -> string -> logcon
  (** Deserialize a biniou value of type {!type:logcon}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type name *)

val name_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!name}.
      Readers may support more than just this tag. *)

val write_untagged_name :
  Bi_outbuf.t -> name -> unit
  (** Output an untagged biniou value of type {!type:name}. *)

val write_name :
  Bi_outbuf.t -> name -> unit
  (** Output a biniou value of type {!type:name}. *)

val string_of_name :
  ?len:int -> name -> string
  (** Serialize a value of type {!type:name} into
      a biniou string. *)

(* Readers for type name *)

val get_name_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> name)
  (** Return a function that reads an untagged
      biniou value of type {!type:name}. *)

val read_name :
  Bi_inbuf.t -> name
  (** Input a tagged biniou value of type {!type:name}. *)

val name_of_string :
  ?pos:int -> string -> name
  (** Deserialize a biniou value of type {!type:name}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type pkind *)

val pkind_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!pkind}.
      Readers may support more than just this tag. *)

val write_untagged_pkind :
  Bi_outbuf.t -> pkind -> unit
  (** Output an untagged biniou value of type {!type:pkind}. *)

val write_pkind :
  Bi_outbuf.t -> pkind -> unit
  (** Output a biniou value of type {!type:pkind}. *)

val string_of_pkind :
  ?len:int -> pkind -> string
  (** Serialize a value of type {!type:pkind} into
      a biniou string. *)

(* Readers for type pkind *)

val get_pkind_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> pkind)
  (** Return a function that reads an untagged
      biniou value of type {!type:pkind}. *)

val read_pkind :
  Bi_inbuf.t -> pkind
  (** Input a tagged biniou value of type {!type:pkind}. *)

val pkind_of_string :
  ?pos:int -> string -> pkind
  (** Deserialize a biniou value of type {!type:pkind}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type uid *)

val uid_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!uid}.
      Readers may support more than just this tag. *)

val write_untagged_uid :
  Bi_outbuf.t -> uid -> unit
  (** Output an untagged biniou value of type {!type:uid}. *)

val write_uid :
  Bi_outbuf.t -> uid -> unit
  (** Output a biniou value of type {!type:uid}. *)

val string_of_uid :
  ?len:int -> uid -> string
  (** Serialize a value of type {!type:uid} into
      a biniou string. *)

(* Readers for type uid *)

val get_uid_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> uid)
  (** Return a function that reads an untagged
      biniou value of type {!type:uid}. *)

val read_uid :
  Bi_inbuf.t -> uid
  (** Input a tagged biniou value of type {!type:uid}. *)

val uid_of_string :
  ?pos:int -> string -> uid
  (** Deserialize a biniou value of type {!type:uid}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type ctxt *)

val ctxt_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!ctxt}.
      Readers may support more than just this tag. *)

val write_untagged_ctxt :
  Bi_outbuf.t -> ctxt -> unit
  (** Output an untagged biniou value of type {!type:ctxt}. *)

val write_ctxt :
  Bi_outbuf.t -> ctxt -> unit
  (** Output a biniou value of type {!type:ctxt}. *)

val string_of_ctxt :
  ?len:int -> ctxt -> string
  (** Serialize a value of type {!type:ctxt} into
      a biniou string. *)

(* Readers for type ctxt *)

val get_ctxt_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> ctxt)
  (** Return a function that reads an untagged
      biniou value of type {!type:ctxt}. *)

val read_ctxt :
  Bi_inbuf.t -> ctxt
  (** Input a tagged biniou value of type {!type:ctxt}. *)

val ctxt_of_string :
  ?pos:int -> string -> ctxt
  (** Deserialize a biniou value of type {!type:ctxt}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type ipath *)

val ipath_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!ipath}.
      Readers may support more than just this tag. *)

val write_untagged_ipath :
  Bi_outbuf.t -> ipath -> unit
  (** Output an untagged biniou value of type {!type:ipath}. *)

val write_ipath :
  Bi_outbuf.t -> ipath -> unit
  (** Output a biniou value of type {!type:ipath}. *)

val string_of_ipath :
  ?len:int -> ipath -> string
  (** Serialize a value of type {!type:ipath} into
      a biniou string. *)

(* Readers for type ipath *)

val get_ipath_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> ipath)
  (** Return a function that reads an untagged
      biniou value of type {!type:ipath}. *)

val read_ipath :
  Bi_inbuf.t -> ipath
  (** Input a tagged biniou value of type {!type:ipath}. *)

val ipath_of_string :
  ?pos:int -> string -> ipath
  (** Deserialize a biniou value of type {!type:ipath}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type vname *)

val vname_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!vname}.
      Readers may support more than just this tag. *)

val write_untagged_vname :
  Bi_outbuf.t -> vname -> unit
  (** Output an untagged biniou value of type {!type:vname}. *)

val write_vname :
  Bi_outbuf.t -> vname -> unit
  (** Output a biniou value of type {!type:vname}. *)

val string_of_vname :
  ?len:int -> vname -> string
  (** Serialize a value of type {!type:vname} into
      a biniou string. *)

(* Readers for type vname *)

val get_vname_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> vname)
  (** Return a function that reads an untagged
      biniou value of type {!type:vname}. *)

val read_vname :
  Bi_inbuf.t -> vname
  (** Input a tagged biniou value of type {!type:vname}. *)

val vname_of_string :
  ?pos:int -> string -> vname
  (** Deserialize a biniou value of type {!type:vname}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type type_ *)

val type__tag : Bi_io.node_tag
  (** Tag used by the writers for type {!type_}.
      Readers may support more than just this tag. *)

val write_untagged_type_ :
  Bi_outbuf.t -> type_ -> unit
  (** Output an untagged biniou value of type {!type:type_}. *)

val write_type_ :
  Bi_outbuf.t -> type_ -> unit
  (** Output a biniou value of type {!type:type_}. *)

val string_of_type_ :
  ?len:int -> type_ -> string
  (** Serialize a value of type {!type:type_} into
      a biniou string. *)

(* Readers for type type_ *)

val get_type__reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> type_)
  (** Return a function that reads an untagged
      biniou value of type {!type:type_}. *)

val read_type_ :
  Bi_inbuf.t -> type_
  (** Input a tagged biniou value of type {!type:type_}. *)

val type__of_string :
  ?pos:int -> string -> type_
  (** Deserialize a biniou value of type {!type:type_}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type expr *)

val expr_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!expr}.
      Readers may support more than just this tag. *)

val write_untagged_expr :
  Bi_outbuf.t -> expr -> unit
  (** Output an untagged biniou value of type {!type:expr}. *)

val write_expr :
  Bi_outbuf.t -> expr -> unit
  (** Output a biniou value of type {!type:expr}. *)

val string_of_expr :
  ?len:int -> expr -> string
  (** Serialize a value of type {!type:expr} into
      a biniou string. *)

(* Readers for type expr *)

val get_expr_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> expr)
  (** Return a function that reads an untagged
      biniou value of type {!type:expr}. *)

val read_expr :
  Bi_inbuf.t -> expr
  (** Input a tagged biniou value of type {!type:expr}. *)

val expr_of_string :
  ?pos:int -> string -> expr
  (** Deserialize a biniou value of type {!type:expr}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type form *)

val form_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!form}.
      Readers may support more than just this tag. *)

val write_untagged_form :
  Bi_outbuf.t -> form -> unit
  (** Output an untagged biniou value of type {!type:form}. *)

val write_form :
  Bi_outbuf.t -> form -> unit
  (** Output a biniou value of type {!type:form}. *)

val string_of_form :
  ?len:int -> form -> string
  (** Serialize a value of type {!type:form} into
      a biniou string. *)

(* Readers for type form *)

val get_form_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> form)
  (** Return a function that reads an untagged
      biniou value of type {!type:form}. *)

val read_form :
  Bi_inbuf.t -> form
  (** Input a tagged biniou value of type {!type:form}. *)

val form_of_string :
  ?pos:int -> string -> form
  (** Deserialize a biniou value of type {!type:form}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type choice *)

val choice_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!choice}.
      Readers may support more than just this tag. *)

val write_untagged_choice :
  Bi_outbuf.t -> choice -> unit
  (** Output an untagged biniou value of type {!type:choice}. *)

val write_choice :
  Bi_outbuf.t -> choice -> unit
  (** Output a biniou value of type {!type:choice}. *)

val string_of_choice :
  ?len:int -> choice -> string
  (** Serialize a value of type {!type:choice} into
      a biniou string. *)

(* Readers for type choice *)

val get_choice_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> choice)
  (** Return a function that reads an untagged
      biniou value of type {!type:choice}. *)

val read_choice :
  Bi_inbuf.t -> choice
  (** Input a tagged biniou value of type {!type:choice}. *)

val choice_of_string :
  ?pos:int -> string -> choice
  (** Deserialize a biniou value of type {!type:choice}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type itrace *)

val itrace_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!itrace}.
      Readers may support more than just this tag. *)

val write_untagged_itrace :
  Bi_outbuf.t -> itrace -> unit
  (** Output an untagged biniou value of type {!type:itrace}. *)

val write_itrace :
  Bi_outbuf.t -> itrace -> unit
  (** Output a biniou value of type {!type:itrace}. *)

val string_of_itrace :
  ?len:int -> itrace -> string
  (** Serialize a value of type {!type:itrace} into
      a biniou string. *)

(* Readers for type itrace *)

val get_itrace_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> itrace)
  (** Return a function that reads an untagged
      biniou value of type {!type:itrace}. *)

val read_itrace :
  Bi_inbuf.t -> itrace
  (** Input a tagged biniou value of type {!type:itrace}. *)

val itrace_of_string :
  ?pos:int -> string -> itrace
  (** Deserialize a biniou value of type {!type:itrace}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type action *)

val action_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!action}.
      Readers may support more than just this tag. *)

val write_untagged_action :
  Bi_outbuf.t -> action -> unit
  (** Output an untagged biniou value of type {!type:action}. *)

val write_action :
  Bi_outbuf.t -> action -> unit
  (** Output a biniou value of type {!type:action}. *)

val string_of_action :
  ?len:int -> action -> string
  (** Serialize a value of type {!type:action} into
      a biniou string. *)

(* Readers for type action *)

val get_action_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> action)
  (** Return a function that reads an untagged
      biniou value of type {!type:action}. *)

val read_action :
  Bi_inbuf.t -> action
  (** Input a tagged biniou value of type {!type:action}. *)

val action_of_string :
  ?pos:int -> string -> action
  (** Deserialize a biniou value of type {!type:action}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type atree *)

val atree_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!atree}.
      Readers may support more than just this tag. *)

val write_untagged_atree :
  Bi_outbuf.t -> atree -> unit
  (** Output an untagged biniou value of type {!type:atree}. *)

val write_atree :
  Bi_outbuf.t -> atree -> unit
  (** Output a biniou value of type {!type:atree}. *)

val string_of_atree :
  ?len:int -> atree -> string
  (** Serialize a value of type {!type:atree} into
      a biniou string. *)

(* Readers for type atree *)

val get_atree_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> atree)
  (** Return a function that reads an untagged
      biniou value of type {!type:atree}. *)

val read_atree :
  Bi_inbuf.t -> atree
  (** Input a tagged biniou value of type {!type:atree}. *)

val atree_of_string :
  ?pos:int -> string -> atree
  (** Deserialize a biniou value of type {!type:atree}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type term *)

val term_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!term}.
      Readers may support more than just this tag. *)

val write_untagged_term :
  Bi_outbuf.t -> term -> unit
  (** Output an untagged biniou value of type {!type:term}. *)

val write_term :
  Bi_outbuf.t -> term -> unit
  (** Output a biniou value of type {!type:term}. *)

val string_of_term :
  ?len:int -> term -> string
  (** Serialize a value of type {!type:term} into
      a biniou string. *)

(* Readers for type term *)

val get_term_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> term)
  (** Return a function that reads an untagged
      biniou value of type {!type:term}. *)

val read_term :
  Bi_inbuf.t -> term
  (** Input a tagged biniou value of type {!type:term}. *)

val term_of_string :
  ?pos:int -> string -> term
  (** Deserialize a biniou value of type {!type:term}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type arity *)

val arity_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!arity}.
      Readers may support more than just this tag. *)

val write_untagged_arity :
  Bi_outbuf.t -> arity -> unit
  (** Output an untagged biniou value of type {!type:arity}. *)

val write_arity :
  Bi_outbuf.t -> arity -> unit
  (** Output a biniou value of type {!type:arity}. *)

val string_of_arity :
  ?len:int -> arity -> string
  (** Serialize a value of type {!type:arity} into
      a biniou string. *)

(* Readers for type arity *)

val get_arity_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> arity)
  (** Return a function that reads an untagged
      biniou value of type {!type:arity}. *)

val read_arity :
  Bi_inbuf.t -> arity
  (** Input a tagged biniou value of type {!type:arity}. *)

val arity_of_string :
  ?pos:int -> string -> arity
  (** Deserialize a biniou value of type {!type:arity}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type sig_ *)

val sig__tag : Bi_io.node_tag
  (** Tag used by the writers for type {!sig_}.
      Readers may support more than just this tag. *)

val write_untagged_sig_ :
  Bi_outbuf.t -> sig_ -> unit
  (** Output an untagged biniou value of type {!type:sig_}. *)

val write_sig_ :
  Bi_outbuf.t -> sig_ -> unit
  (** Output a biniou value of type {!type:sig_}. *)

val string_of_sig_ :
  ?len:int -> sig_ -> string
  (** Serialize a value of type {!type:sig_} into
      a biniou string. *)

(* Readers for type sig_ *)

val get_sig__reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> sig_)
  (** Return a function that reads an untagged
      biniou value of type {!type:sig_}. *)

val read_sig_ :
  Bi_inbuf.t -> sig_
  (** Input a tagged biniou value of type {!type:sig_}. *)

val sig__of_string :
  ?pos:int -> string -> sig_
  (** Deserialize a biniou value of type {!type:sig_}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type bvar *)

val bvar_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!bvar}.
      Readers may support more than just this tag. *)

val write_untagged_bvar :
  Bi_outbuf.t -> bvar -> unit
  (** Output an untagged biniou value of type {!type:bvar}. *)

val write_bvar :
  Bi_outbuf.t -> bvar -> unit
  (** Output a biniou value of type {!type:bvar}. *)

val string_of_bvar :
  ?len:int -> bvar -> string
  (** Serialize a value of type {!type:bvar} into
      a biniou string. *)

(* Readers for type bvar *)

val get_bvar_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> bvar)
  (** Return a function that reads an untagged
      biniou value of type {!type:bvar}. *)

val read_bvar :
  Bi_inbuf.t -> bvar
  (** Input a tagged biniou value of type {!type:bvar}. *)

val bvar_of_string :
  ?pos:int -> string -> bvar
  (** Deserialize a biniou value of type {!type:bvar}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type env *)

val env_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!env}.
      Readers may support more than just this tag. *)

val write_untagged_env :
  Bi_outbuf.t -> env -> unit
  (** Output an untagged biniou value of type {!type:env}. *)

val write_env :
  Bi_outbuf.t -> env -> unit
  (** Output a biniou value of type {!type:env}. *)

val string_of_env :
  ?len:int -> env -> string
  (** Serialize a value of type {!type:env} into
      a biniou string. *)

(* Readers for type env *)

val get_env_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> env)
  (** Return a function that reads an untagged
      biniou value of type {!type:env}. *)

val read_env :
  Bi_inbuf.t -> env
  (** Input a tagged biniou value of type {!type:env}. *)

val env_of_string :
  ?pos:int -> string -> env
  (** Deserialize a biniou value of type {!type:env}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

(* Writers for type goal *)

val goal_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!goal}.
      Readers may support more than just this tag. *)

val write_untagged_goal :
  Bi_outbuf.t -> goal -> unit
  (** Output an untagged biniou value of type {!type:goal}. *)

val write_goal :
  Bi_outbuf.t -> goal -> unit
  (** Output a biniou value of type {!type:goal}. *)

val string_of_goal :
  ?len:int -> goal -> string
  (** Serialize a value of type {!type:goal} into
      a biniou string. *)

(* Readers for type goal *)

val get_goal_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> goal)
  (** Return a function that reads an untagged
      biniou value of type {!type:goal}. *)

val read_goal :
  Bi_inbuf.t -> goal
  (** Input a tagged biniou value of type {!type:goal}. *)

val goal_of_string :
  ?pos:int -> string -> goal
  (** Deserialize a biniou value of type {!type:goal}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

