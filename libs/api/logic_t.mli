(* Auto-generated from "logic.atd" *)
[@@@ocaml.warning "-27-32-33-35-39"]

type bkind = [ `Forall | `Exist ]

type logcon = [ `And | `Or | `Imp | `Equiv | `Not ]

type name = string

type pkind = [ `Hyp | `Concl | `Var of [ `Head | `Body ] ]

type uid = int

type ctxt = { kind: pkind; handle: uid }

type ipath = { root: uid; ctxt: ctxt; sub: int list }

type vname = (name * int)

type type_ = [
    `TVar of vname
  | `TUnit
  | `TProd of (type_ * type_)
  | `TOr of (type_ * type_)
  | `TRec of (name * type_)
]

type expr = [ `EVar of vname | `EFun of (name * expr list) ]

type form = [
    `FTrue
  | `FFalse
  | `FPred of (name * expr list)
  | `FConn of (logcon * form list)
  | `FBind of (bkind * name * type_ * form)
]

type choice = (int * expr option)

type itrace = choice list

type action = [
    `AId
  | `ADef of ((type_ * expr option) * uid)
  | `AIntro of (int * (expr * type_) option)
  | `AElim of uid
  | `ACut of (form * uid)
  | `AAssume of (form * uid)
  | `AGeneralize of uid
  | `AMove of (uid * uid option)
  | `ADuplicate of uid
  | `ALink of (ipath * ipath * itrace)
]

type atree = [ `PNode of (action * atree list) ]

type term = [ `F of form | `E of expr ]

type arity = type_ list

type sig_ = (arity * type_)

type bvar = (type_ * expr option)

type env = {
  env_prp: (name * arity) list;
  env_fun: (name * sig_) list;
  env_var: (name * bvar list) list;
  env_tvar: (name * type_ option list) list;
  env_handles: (vname * uid) list
}

type goal = (env * form list * form)
