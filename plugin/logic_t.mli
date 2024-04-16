(* Auto-generated from "logic.atd" *)
[@@@ocaml.warning "-27-32-33-35-39"]

type varenv = Fo_t.varenv

type uid = string

type type_ = Fo_t.type_

type term = Fo_t.term

type sig_ = Fo_t.sig_

type pkind = [ `Hyp | `Concl | `Var of [ `Head | `Body ] ]

type name = Fo_t.name

type logcon = Fo_t.logcon

type form = Fo_t.form

type hyp = { h_id: uid; h_form: form }

type lgoal = (hyp list * form)

type lenv = Fo_t.lenv

type lemma = { l_user: name; l_full: name; l_stmt: form }

type env = Fo_t.env

type lemmadb = (env * lemma list)

type expr = Fo_t.expr

type choice = (int * (lenv * lenv * expr) option)

type itrace = choice list

type ctxt = { kind: pkind; handle: uid }

type ipath = { ctxt: ctxt; sub: int list }

type goal = { g_env: env; g_hyps: hyp list; g_concl: form }

type goals = goal list

type bvar = Fo_t.bvar

type bkind = Fo_t.bkind

type arity = Fo_t.arity

type aident = (string * lgoal)

type agoal = { a_vars: varenv; a_hyps: hyp list; a_concl: form }

type action = [
    `AId
  | `ADef of (name * type_ * expr)
  | `ALemma of name
  | `AIntro of (int * (expr * type_) option)
  | `AExact of uid
  | `AElim of (uid * int)
  | `AInd of uid
  | `ASimpl of ipath
  | `ARed of ipath
  | `AIndt of ipath
  | `APbp of ipath
  | `ACase of ipath
  | `ACut of form
  | `AGeneralize of uid
  | `AMove of (uid * uid option)
  | `ADuplicate of uid
  | `ALink of (ipath * ipath * itrace)
  | `AInstantiate of (expr * ipath)
]
