open Proofview

let message = "Welcome to Actema!"

let dummy_form : Logic_t.form =
  `FPred ("dummy", [])

let form_of_types (evd : Evd.evar_map) (t : EConstr.types) : Logic_t.form =
  try
    let prod = EConstr.destProd evd t in
    dummy_form
  with Constr.DestKO ->
    dummy_form

let export_goal (goal : Goal.t) : Logic_t.goal =
  let evd = Goal.sigma goal in
  let coq_hyps = Goal.hyps goal in
  let coq_concl = Goal.concl goal in

  let env : Logic_t.env =
    { env_prp = [];
      env_fun = [];
      env_var = [];
      env_tvar = [];
      env_handles = [] } in

  let hyps : Logic_t.form list =
    [] in

  let concl : Logic_t.form =
    form_of_types evd coq_concl in
  
  env, hyps, concl

let biniou_unhash_dict = Bi_io.make_unhash [
  "EVar"; "EFun";
  "And"; "Or"; "Imp"; "Equiv"; "Not";
  "Forall"; "Exist";
  "FTrue"; "FFalse"; "FPred"; "FConn"; "FBind";
  "F"; "E";
  "Hyp"; "Concl"; "Var"; "Head"; "Body";
  "kind"; "pkind"; "handle";
  "root"; "uid"; "ctxt"; "sub";
  "AId"; "ADef"; "AIntro"; "AElim"; "ACut"; "AAssume"; "AGeneralize"; "AMove"; "ADuplicate"; "ALink";
  "PNode";
  "env_prp"; "env_fun"; "env_var"; "env_tvar"; "env_handles";
]

let string_of_goal goal =
  Bi_io.view ~unhash:biniou_unhash_dict (Logic_b.string_of_goal goal)

let proofstate_tac =
  Goal.enter begin fun coq_goal ->
    let goal = export_goal coq_goal in
    let goal_str = string_of_goal goal in
    Feedback.msg_notice (Pp.str goal_str);
    Tacticals.tclIDTAC
  end