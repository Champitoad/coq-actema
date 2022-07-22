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

let string_of_atree t =
  Bi_io.view ~unhash:biniou_unhash_dict (Logic_b.string_of_atree t)