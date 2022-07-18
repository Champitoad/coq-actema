open Proofview

let message = "Welcome to Actema!"

let dummy_form : Logic_t.form =
  `FPred ("dummy", [])

type fdest = ((Environ.env * Evd.evar_map) * EConstr.types) -> Logic_t.form

let comp_fdest (d1 : fdest) (d2 : fdest) : fdest = fun (e, t) ->
  try d1 (e, t) with Constr.DestKO -> d2 (e, t)

let ( >>! ) = comp_fdest

let is_prop env evd term =
  let sort = Retyping.get_sort_of env evd term in
  Sorts.is_prop sort

let is_imp (env, evd) x t1 t2 : bool = 
  Printf.printf "%b" (is_prop env evd t1);
  is_prop env evd t1
  && is_prop
       (EConstr.push_rel (Context.Rel.Declaration.LocalAssum (x, t1)) env)
       evd t2
  && (x.Context.binder_name = Names.Anonymous || EConstr.Vars.noccurn evd 1 t2)

let rec dest_imp : fdest = fun ((_, evd as e), t) ->
  let x, t1, t2 = EConstr.destProd evd t in
  if not (is_imp e x t1 t2) then raise Constr.DestKO;
  `FConn (`Imp, [dest_form (e, t1); dest_form (e, t2)])

and dest_form : fdest = fun et ->
  begin
    dest_imp >>!
    fun _ -> dummy_form
  end et

let export_goal (goal : Goal.t) : Logic_t.goal =
  let coq_env = Goal.env goal in
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
    dest_form ((coq_env, evd), coq_concl) in
  
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