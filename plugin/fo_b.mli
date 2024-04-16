(* Auto-generated from "fo.atd" *)
[@@@ocaml.warning "-27-32-33-35-39"]

type bkind = Fo_t.bkind

type logcon = Fo_t.logcon

type name = Fo_t.name

type type_ = Fo_t.type_

type expr = Fo_t.expr

type form = Fo_t.form

type bvar = Fo_t.bvar

type varenv = Fo_t.varenv

type term = Fo_t.term

type arity = Fo_t.arity

type sig_ = Fo_t.sig_

type lenv = Fo_t.lenv

type env = Fo_t.env = {
  env_sort: name list;
  env_prp: (name * arity) list;
  env_fun: (name * sig_) list;
  env_sort_name: (name * name) list;
  env_prp_name: (name * name) list;
  env_fun_name: (name * name) list;
  env_var: varenv
}

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

(* Writers for type varenv *)

val varenv_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!varenv}.
      Readers may support more than just this tag. *)

val write_untagged_varenv :
  Bi_outbuf.t -> varenv -> unit
  (** Output an untagged biniou value of type {!type:varenv}. *)

val write_varenv :
  Bi_outbuf.t -> varenv -> unit
  (** Output a biniou value of type {!type:varenv}. *)

val string_of_varenv :
  ?len:int -> varenv -> string
  (** Serialize a value of type {!type:varenv} into
      a biniou string. *)

(* Readers for type varenv *)

val get_varenv_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> varenv)
  (** Return a function that reads an untagged
      biniou value of type {!type:varenv}. *)

val read_varenv :
  Bi_inbuf.t -> varenv
  (** Input a tagged biniou value of type {!type:varenv}. *)

val varenv_of_string :
  ?pos:int -> string -> varenv
  (** Deserialize a biniou value of type {!type:varenv}.
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

(* Writers for type lenv *)

val lenv_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!lenv}.
      Readers may support more than just this tag. *)

val write_untagged_lenv :
  Bi_outbuf.t -> lenv -> unit
  (** Output an untagged biniou value of type {!type:lenv}. *)

val write_lenv :
  Bi_outbuf.t -> lenv -> unit
  (** Output a biniou value of type {!type:lenv}. *)

val string_of_lenv :
  ?len:int -> lenv -> string
  (** Serialize a value of type {!type:lenv} into
      a biniou string. *)

(* Readers for type lenv *)

val get_lenv_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> lenv)
  (** Return a function that reads an untagged
      biniou value of type {!type:lenv}. *)

val read_lenv :
  Bi_inbuf.t -> lenv
  (** Input a tagged biniou value of type {!type:lenv}. *)

val lenv_of_string :
  ?pos:int -> string -> lenv
  (** Deserialize a biniou value of type {!type:lenv}.
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

