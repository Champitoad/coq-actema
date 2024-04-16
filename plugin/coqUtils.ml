open Proofview

module PVMonad = struct
  include Proofview.Monad
  let (let*) = (>>=)
end

module Log = struct
  let str (str : string) =
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

  let univ_levels evd =
    let univs : string list =
      Evd.evar_universe_context evd |> UState.ugraph |>
      UGraph.domain |> Univ.Level.Set.elements |>
      List.map Univ.Level.to_string in
    str Extlib.(List.to_string identity univs)

  let profile (name : string) (chunk : unit -> 'a) : 'a =
    let start = Sys.time () in
    let result = chunk () in
    let end_ = Sys.time () in
    let duration = end_ -. start in
    str (Printf.sprintf "%s took %f seconds" name duration);
    result
end

let name_of_const evd t =
  EConstr.destConst evd t |> fst |>
  Names.Constant.label |> Names.Label.to_string

let name_of_inductive env evd t =
  let name, _ = EConstr.destInd evd t in
  Printer.pr_inductive env name |> Pp.string_of_ppcmds

let kername (path : string list) (name : string) =
  let open Names in
  let dir = DirPath.make (path |> List.rev |> List.map Id.of_string) in
  KerName.make (ModPath.MPfile dir) (Label.make name)

let const_kname evd t =
  EConstr.destConst evd t |> fst |> Names.Constant.user

let ind_body env (ind : Names.inductive) : Declarations.one_inductive_body =
  let spec = Inductive.lookup_mind_specif env ind in
  let Declarations.({ mind_packets; _ }, _) = spec in
  mind_packets.(snd ind)

let kname_of_inductive env (ind : Names.inductive) : Names.KerName.t =
  let body = ind_body env ind in
  let modpath = Names.Ind.modpath ind in
  let label = body.Declarations.mind_typename |> Names.Label.of_id in
  Names.KerName.make modpath label

let arity_of_inductive env (ind : Names.inductive) : EConstr.t =
  let body = ind_body env ind in
  match body.Declarations.mind_arity with
  | RegularArity ar -> EConstr.of_constr ar.mind_user_arity
  | TemplateArity ar -> (*EConstr.mkType ar.template_level*) failwith "TODO"

let kname_of_constructor env (c : Names.Construct.t) : Names.KerName.t =
  let ind = Names.inductive_of_constructor c in
  let body = ind_body env ind in
  let i = Names.index_of_constructor c in
  let label = body.mind_consnames.(i-1) |> Names.Label.of_id in
  let modpath = Names.Construct.modpath c in
  Names.KerName.make modpath label

let type_of_constructor env (c : Names.Construct.t) : EConstr.t =
  let ind = Names.inductive_of_constructor c in
  let ind_body = ind_body env ind in
  let i = Names.index_of_constructor c in
  let ty = ind_body.mind_user_lc.(i-1) in
  EConstr.of_constr ty

let construct_kname env evd (t : EConstr.t) : Names.KerName.t =
  let c = EConstr.destConstruct evd t |> fst in
  kname_of_constructor env c

let ind_kname evd t =
  EConstr.destInd evd t |> fst |> fst |> Names.MutInd.canonical

let calltac (tacname : Names.KerName.t) (args : EConstr.constr list) : unit tactic =
  let open Ltac_plugin in
  let open Tacexpr in
  let open Tacinterp in
  let open Names in
  let open Locus in
  let ltac_call tac (args:glob_tactic_arg list) =
    CAst.make @@ TacArg (TacCall (CAst.make (ArgArg(Loc.tag @@ Lazy.force tac),args)))
  in
  let f = lazy tacname in
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
    let name = Names.KerName.to_string tacname in
    let _ = Log.error (Printf.sprintf "Could not find tactic \"%s\"" name) in
    PVMonad.return ()

module Trm = struct
  open EConstr

  let var name =
    EConstr.mkVar (Names.Id.of_string name)
  
  let lambda x ty body =
    let x = Context.annotR (Names.Id.of_string x) in
    (*mkNamedLambda x ty body*)
    failwith "todo"
  
  let dprod x ty body =
    let x = Context.nameR (Names.Id.of_string x) in
    mkProd (x, ty, body)

  module Logic = struct
    let kname = kername ["Coq"; "Init"; "Logic"]

    let eq_ind (mind, i) name =
      Names.(KerName.equal (MutInd.canonical mind) (kname name)) && i = 0

    let true_ =
      UnsafeMonomorphic.mkInd (Names.MutInd.make1 (kname "True"), 0)

    let false_ =
      UnsafeMonomorphic.mkInd (Names.MutInd.make1 (kname "True"), 0)

    let and_ f1 f2 =
      let and_ = UnsafeMonomorphic.mkInd (Names.MutInd.make1 (kname "and"), 0) in
      mkApp (and_, [|f1; f2|])

    let or_ f1 f2 =
      let or_ = UnsafeMonomorphic.mkInd (Names.MutInd.make1 (kname "or"), 0) in
      mkApp (or_, [|f1; f2|])
    
    let imp f1 f2 =
      dprod "dummy" f1 f2
    
    let not f =
      let not = mkConst (Names.Constant.make1 (kname "not")) in
      mkApp (not, [|f|])

    let iff f1 f2 =
      let iff = mkConst (Names.Constant.make1 (kname "iff")) in
      mkApp (iff, [|f1; f2|])
    
    let ex x ty body =
      let ex = UnsafeMonomorphic.mkInd (Names.MutInd.make1 (kname "ex"), 0) in
      let p = lambda x ty body in
      mkApp (ex, [|ty; p|])
    
    let fa x ty body =
      dprod x ty body

    let eq ty =
      let eq = UnsafeMonomorphic.mkInd (Names.MutInd.make1 (kname "eq"), 0) in
      mkApp (eq, [|ty|])
  end

  let type_ =
    EConstr.mkSort (ESorts.type1)

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
  
  let add_modpaths = [
    ["Coq"; "Arith"; "PeanoNat"; "Nat"];
    ["Coq"; "Init"; "Nat"];
  ]
  let add_knames =
    List.map (fun mp -> kername mp "add") add_modpaths
  
  let mul_modpaths = add_modpaths
  let mul_knames =
    List.map (fun mp -> kername mp "mul") mul_modpaths
  
  let app_kname =
    kername ["Coq"; "Init"; "Datatypes"] "app"

  let sigT_kname =
    kername ["Coq"; "Init"; "Specif"] "sigT"
  
  let nat_name : Names.inductive =
    Names.MutInd.make1 nat_kname, 0
  let nat =
    UnsafeMonomorphic.mkInd nat_name

  let bool_name =
    (Names.MutInd.make1 bool_kname, 0)
  let bool =
    UnsafeMonomorphic.mkInd bool_name

  let unit =
    UnsafeMonomorphic.mkInd (Names.MutInd.make1 unit_kname, 0)
  
  let prod_name : Names.inductive =
    Names.MutInd.make1 prod_kname, 0
  let prod t1 t2 =
    let prod = UnsafeMonomorphic.mkInd prod_name in
    mkApp (prod, [| t1; t2 |])
  
  let sigT_name : Names.inductive =
    Names.MutInd.make1 sigT_kname, 0
  let sigT x ty p =
    let sigT = UnsafeMonomorphic.mkInd sigT_name in
    mkApp (sigT, [| ty; lambda x ty p |])
  
  let option_name : Names.inductive =
    Names.MutInd.make1 option_kname, 0
  let option ty =
    let option = UnsafeMonomorphic.mkInd option_name in
    mkApp (option, [| ty |])
  
  let list_name : Names.inductive =
    Names.MutInd.make1 list_kname, 0
  let list ty =
    let list = UnsafeMonomorphic.mkInd list_name in
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
  let existT x ty p w t =
    let existT = mkConstruct existT_name in
    mkApp (existT, [| ty; lambda x ty p; w; t |])
  
  let none_name : Names.constructor =
    option_name, 2
  let none ty =
    let none = mkConstruct none_name in
    mkApp (none, [| ty |])

  let some_name : Names.constructor =
    option_name, 1
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
  
  let add_names : Names.Constant.t list =
    List.map Names.Constant.make1 add_knames

  let mul_names : Names.Constant.t list =
    List.map Names.Constant.make1 mul_knames

  let app_name : Names.Constant.t =
    Names.Constant.make1 app_kname
  
  
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
    | None -> none ty
    | Some x -> some ty (cast x)
end

module Goal = struct
  include Goal

  let hyps_names (goal : Goal.t) =
    hyps goal |> Context.Named.to_vars
  
  let fresh_name ?(basename = "H") =
    let base_name = Names.Id.of_string basename in
    fun goal ->
      let hyps_names = hyps_names goal in
      fun () ->
        Namegen.next_ident_away base_name hyps_names
end