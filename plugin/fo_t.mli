(* Auto-generated from "fo.atd" *)
[@@@ocaml.warning "-27-32-33-35-39"]

type bkind = [ `Forall | `Exist ]

type logcon = [ `And | `Or | `Imp | `Equiv | `Not ]

type name = string

type type_ = [ `TVar of name ]

type expr = [ `EVar of name | `EFun of (name * expr list) ]

type form = [
    `FTrue
  | `FFalse
  | `FPred of (name * expr list)
  | `FConn of (logcon * form list)
  | `FBind of (bkind * name * type_ * form)
]

type bvar = (type_ * expr option)

type varenv = (name * bvar) list

type term = [ `F of form | `E of expr ]

type arity = type_ list

type sig_ = (arity * type_)

type lenv = (name * type_) list

type env = {
  env_sort: name list;
  env_prp: (name * arity) list;
  env_fun: (name * sig_) list;
  env_sort_name: (name * name) list;
  env_prp_name: (name * name) list;
  env_fun_name: (name * name) list;
  env_var: varenv
}
