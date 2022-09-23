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

  let get (env : env) ((name, idx) : vname) =
    let bds = List.assoc_opt name env.env_var in
    Stdlib.Option.fold ~none:None ~some:(fun bds -> List.nth_opt bds idx) bds

  let push (env : env) ((name, bvar) : name * bvar) =
    let bds =
      match List.assoc_opt name env.env_var with
      | None -> []
      | Some bds -> bds in

    let env_var = (name, bvar :: bds) :: env.env_var in

    let env_handles = 
      ((name, List.length bds), fresh ()) :: env.env_handles in

    { env with env_var; env_handles }
  
  let push_lenv (env : env) (lenv : lenv) : env =
    List.fold_left begin fun env (x, ty) ->
        push env (x, (ty, None))
      end env lenv
end

module Funs = struct
  let get (env : env) (name : name) =
    List.assoc_opt name env.env_fun
end

exception TypingError

let rec t_equal env ty1 ty2 =
  match ty1, ty2 with
  | `TVar a, `TVar b ->
      a = b

  | `TUnit, `TUnit ->
      true
    
  | `TProd (tya1, tyb1), `TProd (tya2, tyb2)
  | `TOr   (tya1, tyb1), `TOr   (tya2, tyb2) ->
         t_equal env tya1 tya2
      && t_equal env tyb1 tyb2

  | `TRec _, `TRec _ ->
      failwith "Unsupported type"

  | _, _ ->
      false

let rec einfer (env : env) (e : expr) : type_ =
  match e with
  | `EVar x -> begin
      match Vars.get env x with
      | None          -> raise TypingError
      | Some (xty, _) -> xty
    end

  | `EFun (f, args) -> begin
      match Funs.get env f with
      | None -> raise TypingError
      | Some (fargs, fres) ->
          if List.length fargs <> List.length args then
            raise TypingError;
          let args = List.map (einfer env) args in
          if not (List.for_all2 (t_equal env) fargs args) then
            raise TypingError;
          fres
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