open Logic_t

module Uid : sig
  include Map.OrderedType

  val fresh : unit -> unit -> t
end with type t = Logic_t.uid = struct
  type t = Logic_t.uid
  
  let compare = Int.compare

  let fresh () : unit -> t =
    let count = ref (-1) in
    fun () -> incr count; !count
end

module Vars = struct
  let fresh = Uid.fresh ()

  let push (env : env) ((name, bvar) : name * bvar) =
    let bds =
      match List.assoc_opt name env.env_var with
      | None -> []
      | Some bds -> bds in

    let env_var = (name, bvar :: bds) :: env.env_var in

    let env_handles = 
      ((name, List.length bds), fresh ()) :: env.env_handles in

    { env with env_var; env_handles }
end

let biniou_unhash_dict = Bi_io.make_unhash [
  "TVar"; "TUnit"; "TProd"; "TOr"; "TRec";
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

let empty_env =
  Fo_t.{ env_prp = []; env_fun = []; env_var = []; env_tvar = []; env_handles = [] }

let string_of_expr e =
  Bi_io.view ~unhash:biniou_unhash_dict (Logic_b.string_of_expr e)

let string_of_form f =
  Bi_io.view ~unhash:biniou_unhash_dict (Logic_b.string_of_form f)

let string_of_goal goal =
  Bi_io.view ~unhash:biniou_unhash_dict (Logic_b.string_of_goal goal)

let string_of_proof prf =
  Bi_io.view ~unhash:biniou_unhash_dict (Logic_b.string_of_proof prf)

let get_hyp ({ g_hyps; _ } : goal) (id : uid) : hyp =
  List.find (fun { h_id; _ } -> h_id = id) g_hyps