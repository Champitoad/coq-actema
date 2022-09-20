open Proofview

module Log = struct
  let str str =
    Feedback.msg_notice (Pp.str str)

  let error msg =
    CErrors.user_err (Pp.str msg)

  let string_of_econstr env evd (t : EConstr.t) : string =
    let pp = Printer.pr_constr_env env evd (EConstr.to_constr evd t) in
    Pp.string_of_ppcmds pp

  let econstr env evd t =
    string_of_econstr env evd t |> str

  let econstr_debug evd t =
    t |> EConstr.to_constr evd |> Constr.debug_print |>
    Feedback.msg_notice
end

let name_of_const evd t =
  EConstr.destConst evd t |> fst |>
  Names.Constant.repr2 |> snd |> Names.Label.to_string

let name_of_inductive env evd t =
  let name, _ = EConstr.destInd evd t in
  Printer.pr_inductive env name |> Pp.string_of_ppcmds

let kername (path : string list) (name : string) =
  let open Names in
  let dir = DirPath.make (path |> List.rev |> List.map Id.of_string) in
  KerName.make (ModPath.MPfile dir) (Label.make name)

let const_kname evd t =
  EConstr.destConst evd t |> fst |> Names.Constant.user

let kname_of_constructor env (c : Names.Construct.t) : Names.KerName.t =
  let ind = Names.inductive_of_constructor c in
  let spec = Inductive.lookup_mind_specif env ind in
  let Declarations.({ mind_packets; _ }, _) = spec in
  let ind_body = mind_packets.(snd ind) in
  let modpath = Names.Construct.modpath c in
  let i = Names.index_of_constructor c in
  let label = ind_body.mind_consnames.(i-1) |> Names.Label.of_id in
  Names.KerName.make modpath label

let construct_kname env evd (t : EConstr.t) : Names.KerName.t =
  let c = EConstr.destConstruct evd t |> fst in
  kname_of_constructor env c

let ind_kname evd t =
  EConstr.destInd evd t |> fst |> fst |> Names.MutInd.canonical

let calltac (tacname : string) (args : EConstr.constr list) : unit tactic =
  let open Ltac_plugin in
  let open Tacexpr in
  let open Tacinterp in
  let open Names in
  let open Locus in
  let ltac_call tac (args:glob_tactic_arg list) =
    CAst.make @@ TacArg (TacCall (CAst.make (ArgArg(Loc.tag @@ Lazy.force tac),args)))
  in
  let f = lazy (kername ["Actema"; "DnD"] tacname) in
  let fold arg (i, vars, lfun) =
    let id = Id.of_string ("x" ^ string_of_int i) in
    let x = Reference (ArgVar CAst.(make id)) in
    (succ i, x :: vars, Id.Map.add id (Value.of_constr arg) lfun)
  in
  let (_, args, lfun) = List.fold_right fold args (0, [], Id.Map.empty) in
  let ist = { (Tacinterp.default_ist ()) with Tacinterp.lfun = lfun; } in
  try
    Tacinterp.eval_tactic_ist ist (ltac_call f args)
  with Not_found ->
    let _ = Log.error (Printf.sprintf "Could not find tactic \"%s\"" tacname) in
    Proofview.Monad.return ()

module Trm = struct
  open EConstr

  let type_ =
    EConstr.mkSort (Sorts.type1)

  let list_kname =
    kername ["Coq"; "Init"; "Datatypes"] "list"
  
  let nat_kname =
    kername ["Coq"; "Init"; "Datatypes"] "nat"

  let bool_kname =
    kername ["Coq"; "Init"; "Datatypes"] "bool"
  
  let unit_kname =
    kername ["Coq"; "Init"; "Datatypes"] "unit"
  
  let prod_kname =
    kername ["Coq"; "Init"; "Datatypes"] "prod"
  
  let option_kname =
    kername ["Coq"; "Init"; "Datatypes"] "option"
  
  let zero_kname =
    kername ["Coq"; "Init"; "Datatypes"] "O"

  let succ_kname =
    kername ["Coq"; "Init"; "Datatypes"] "S"
  
  let add_kname =
    kername ["Coq"; "Init"; "Nat"] "add"
  
  let mul_kname =
    kername ["Coq"; "Init"; "Nat"] "mul"
  
  let eq_kname =
    kername ["Coq"; "Init"; "Logic"] "eq"
  
  let ex_kname =
    kername ["Coq"; "Init"; "Logic"] "ex"

  let sigT_kname =
    kername ["Coq"; "Init"; "Specif"] "sigT"
  
  let nat_name : Names.inductive =
    Names.MutInd.make1 nat_kname, 0
  let nat =
    mkInd nat_name

  let bool =
    mkInd (Names.MutInd.make1 bool_kname, 0)

  let unit =
    mkInd (Names.MutInd.make1 unit_kname, 0)
  
  let prod_name : Names.inductive =
    Names.MutInd.make1 prod_kname, 0
  let prod t1 t2 =
    let prod = mkInd prod_name in
    mkApp (prod, [| t1; t2 |])
  
  let sigT_name : Names.inductive =
    Names.MutInd.make1 sigT_kname, 0
  let sigT ty p =
    let sigT = mkInd sigT_name in
    mkApp (sigT, [| ty; p |])
  
  let option_name : Names.inductive =
    Names.MutInd.make1 option_kname, 0
  let option ty =
    let option = mkInd option_name in
    mkApp (option, [| ty |])
  
  let eq ty =
    let eq = mkInd (Names.MutInd.make1 eq_kname, 0) in
    mkApp (eq, [|ty|])
  
  let list_name : Names.inductive =
    Names.MutInd.make1 list_kname, 0
  let list ty =
    let list = mkInd list_name in
    mkApp (list, [| ty |])
  
  let nil ty =
    let nil = mkConstruct ((Names.MutInd.make1 list_kname, 0), 1) in
    mkApp (nil, [|ty|])

  let cons ty x l =
    let cons = mkConstruct ((Names.MutInd.make1 list_kname, 0), 2) in
    mkApp (cons, [|ty; x; l|])

  let pair_name : Names.constructor =
    prod_name, 1
  let pair ty1 ty2 t1 t2 =
    let pair = mkConstruct pair_name in
    mkApp (pair, [| ty1; ty2; t1; t2 |])
  
  let existT_name : Names.constructor =
    sigT_name, 1
  let existT ty p w t =
    let existT = mkConstruct existT_name in
    mkApp (existT, [| ty; p; w; t |])
  
  let none_name : Names.constructor =
    option_name, 1
  let none =
    mkConstruct none_name

  let some_name : Names.constructor =
    option_name, 2
  let some ty t =
    let some = mkConstruct some_name in
    mkApp (some, [|ty; t|])
  
  let zero_name : Names.constructor =
    (Names.MutInd.make1 nat_kname, 0), 1
  let zero =
    mkConstruct zero_name

  let succ_name : Names.constructor =
    (Names.MutInd.make1 nat_kname, 0), 2
  let succ n =
    let succ = mkConstruct succ_name in
    mkApp (succ, [|n|])
  
  let add_name : Names.Constant.t =
    Names.Constant.make1 add_kname

  let mul_name : Names.Constant.t =
    Names.Constant.make1 mul_kname
  
  let tt =
    mkConstruct ((Names.MutInd.make1 unit_kname, 0), 1)
  
  let rec nat_of_int n =
    match n with
    | 0 -> zero
    | _ -> succ (nat_of_int (n-1))
  
  let bool_of_bool b =
    match b with
    | true -> mkConstruct ((Names.MutInd.make1 bool_kname, 0), 1)
    | false -> mkConstruct ((Names.MutInd.make1 bool_kname, 0), 2)
  
  let of_list ty cast l =
    List.fold_right (fun x t -> cons ty (cast x) t) l (nil ty)
  
  let natlist =
    of_list nat nat_of_int
  
  let boollist =
    of_list bool bool_of_bool
  
  let of_option ty cast o =
    match o with
    | None -> none
    | Some x -> some ty (cast x)
end