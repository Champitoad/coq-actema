open Proofview

module Array = struct
  include Array

  let get_opt a n =
    try Some a.(n)
    with Invalid_argument _ -> None
end

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

let kername (path : string list) (name : string) =
  let open Names in
  let dir = DirPath.make (path |> List.rev |> List.map Id.of_string) in
  KerName.make (ModPath.MPfile dir) (Label.make name)

let construct_kname env (c : Names.Construct.t) : Names.KerName.t =
  let ind = Names.inductive_of_constructor c in
  let spec = Inductive.lookup_mind_specif env ind in
  let Declarations.({ mind_packets; _ }, _) = spec in
  let ind_body = mind_packets.(snd ind) in
  let modpath = Names.Construct.modpath c in
  let i = Names.index_of_constructor c in
  let label = ind_body.mind_consnames.(i-1) |> Names.Label.of_id in
  Names.KerName.make modpath label

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

  let list_kname =
    kername ["Coq"; "Init"; "Datatypes"] "list"
  
  let nat_kname =
    kername ["Coq"; "Init"; "Datatypes"] "nat"

  let bool_kname =
    kername ["Coq"; "Init"; "Datatypes"] "bool"
  
  let unit_kname =
    kername ["Coq"; "Init"; "Datatypes"] "unit"
  
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
  
  let nat =
    mkInd (Names.MutInd.make1 nat_kname, 0)

  let bool =
    mkInd (Names.MutInd.make1 bool_kname, 0)

  let unit =
    mkInd (Names.MutInd.make1 unit_kname, 0)
  
  let eq ty =
    let eq = mkInd (Names.MutInd.make1 eq_kname, 0) in
    mkApp (eq, [|ty|])

  let nil ty =
    let nil = mkConstruct ((Names.MutInd.make1 list_kname, 0), 1) in
    mkApp (nil, [|ty|])

  let cons ty x l =
    let cons = mkConstruct ((Names.MutInd.make1 list_kname, 0), 2) in
    mkApp (cons, [|ty; x; l|])
  
  let zero =
    mkConstruct ((Names.MutInd.make1 nat_kname, 0), 1)

  let succ n =
    let succ = mkConstruct ((Names.MutInd.make1 nat_kname, 0), 2) in
    mkApp (succ, [|n|])
  
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
end