let biniou_unhash_dict = Bi_io.make_unhash [
  "EVar"; "EFun";
  "And"; "Or"; "Imp"; "Equiv"; "Not";
  "Forall"; "Exist";
  "FTrue"; "FFalse"; "FPred"; "FConn"; "FBind";
  "F"; "E";
  "env_prp"; "env_fun"; "env_var"; "env_tvar"; "env_handles";
  "h_id"; "h_form";
  "g_env"; "g_hyps"; "g_concl";
  "Hyp"; "Concl"; "Var"; "Head"; "Body";
  "kind"; "pkind"; "handle";
  "root"; "uid"; "ctxt"; "sub";
  "AId"; "ADef"; "AIntro"; "AElim"; "AExact"; "ACut"; "AAssume"; "AGeneralize"; "AMove"; "ADuplicate"; "ALink";
  "PNode";
]

let string_of_goal goal =
  Bi_io.view ~unhash:biniou_unhash_dict (Logic_b.string_of_goal goal)

let string_of_proof prf =
  Bi_io.view ~unhash:biniou_unhash_dict (Logic_b.string_of_proof prf)