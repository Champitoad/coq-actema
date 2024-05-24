open Utils.Pervasive
open Proofview

(** A thin wrapper around Proofview.Monad.
    Introduces some standard monad notations.*)
module PVMonad = struct
  include Proofview.Monad

  let ( let* ) = ( >>= )
end

(** Use this module when logging in the plugin. *)
module Log = struct
  let str (str : string) = Feedback.msg_notice (Pp.str str)
  let printf fmt = Format.ksprintf str fmt
  let error msg = CErrors.user_err (Pp.str msg)

  let string_of_econstr env evd (t : EConstr.t) : string =
    let pp = Printer.pr_constr_env env evd (EConstr.to_constr evd t) in
    Pp.string_of_ppcmds pp

  let econstr env evd t = string_of_econstr env evd t |> str

  let econstr_debug evd t =
    t |> EConstr.to_constr evd |> Constr.debug_print |> Feedback.msg_notice

  let univ_levels evd =
    let univs : string list =
      Evd.evar_universe_context evd
      |> UState.ugraph |> UGraph.domain |> Univ.Level.Set.elements
      |> List.map Univ.Level.to_string
    in
    str (List.to_string Fun.id univs)

  let profile (name : string) (chunk : unit -> 'a) : 'a =
    let start = Sys.time () in
    let result = chunk () in
    let end_ = Sys.time () in
    let duration = end_ -. start in
    str (Printf.sprintf "%s took %f seconds" name duration);
    result
end

let name_of_const evd t =
  EConstr.destConst evd t |> fst |> Names.Constant.label
  |> Names.Label.to_string

let name_of_inductive env evd t =
  let name, _ = EConstr.destInd evd t in
  Printer.pr_inductive env name |> Pp.string_of_ppcmds

let kername (path : string list) (name : string) =
  let open Names in
  let dir = DirPath.make (path |> List.rev |> List.map Id.of_string) in
  KerName.make (ModPath.MPfile dir) (Label.make name)

let const_kname evd t = EConstr.destConst evd t |> fst |> Names.Constant.user

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
  | TemplateArity ar -> EConstr.mkSort @@ EConstr.ESorts.make ar.template_level

let kname_of_constructor env (c : Names.Construct.t) : Names.KerName.t =
  let ind = Names.inductive_of_constructor c in
  let body = ind_body env ind in
  let i = Names.index_of_constructor c in
  let label = body.mind_consnames.(i - 1) |> Names.Label.of_id in
  let modpath = Names.Construct.modpath c in
  Names.KerName.make modpath label

let type_of_constructor env (c : Names.Construct.t) : EConstr.t =
  let ind = Names.inductive_of_constructor c in
  let ind_body = ind_body env ind in
  let i = Names.index_of_constructor c in
  let ty = ind_body.mind_user_lc.(i - 1) in
  EConstr.of_constr ty

let construct_kname env evd (t : EConstr.t) : Names.KerName.t =
  let c = EConstr.destConstruct evd t |> fst in
  kname_of_constructor env c

let ind_kname evd t =
  EConstr.destInd evd t |> fst |> fst |> Names.MutInd.canonical

let calltac (tacname : Names.KerName.t) (args : EConstr.constr list) :
    unit tactic =
  let open Ltac_plugin in
  let open Tacexpr in
  let open Tacinterp in
  let open Names in
  let open Locus in
  let ltac_call tac (args : glob_tactic_arg list) =
    CAst.make
    @@ TacArg (TacCall (CAst.make (ArgArg (Loc.tag @@ Lazy.force tac), args)))
  in
  let f = lazy tacname in
  let fold arg (i, vars, lfun) =
    let id = Id.of_string ("x" ^ string_of_int i) in
    let x = Reference (ArgVar CAst.(make id)) in
    (succ i, x :: vars, Id.Map.add id (Value.of_constr arg) lfun)
  in
  let _, args, lfun = List.fold_right fold args (0, [], Id.Map.empty) in
  let ist = { (Tacinterp.default_ist ()) with Tacinterp.lfun } in
  try Tacinterp.eval_tactic_ist ist (ltac_call f args)
  with Not_found ->
    let name = Names.KerName.to_string tacname in
    let _ = Log.error (Printf.sprintf "Could not find tactic \"%s\"" name) in
    PVMonad.return ()

(** Utilities to construct common Coq terms. *)
module Trm = struct
  let mkVar name = EConstr.mkVar (Names.Id.of_string name)

  (** Utility to make a constant, taking care to instantiate universes. *)
  let mkConst env path name =
    let name = Names.Constant.make1 (kername path name) in
    let (_, inst), _ = UnivGen.fresh_constant_instance env name in
    EConstr.mkConstU (name, EConstr.EInstance.make inst)

  (** Utility to make an inductive, taking care to instantiate universes.
      The integer parameter is the index of the inductive in the mutual inductive block
      (it starts at 0). *)
  let mkInd ?(index = 0) env path name =
    let name = (Names.MutInd.make1 (kername path name), index) in
    let (_, inst), _ = UnivGen.fresh_inductive_instance env name in
    EConstr.mkIndU (name, EConstr.EInstance.make inst)

  (** Utility to make an inductive constructor, taking care to instantiate universes.
      The integer parameters are the index of the inductive in the mutual inductive block
      (it starts at 0) and the index of the constructor (it starts at 1). *)
  let mkConstruct ?(index = 0) ~constructor env path name =
    let name = ((Names.MutInd.make1 (kername path name), index), constructor) in
    let (_, inst), _ = UnivGen.fresh_constructor_instance env name in
    EConstr.mkConstructU (name, EConstr.EInstance.make inst)

  let lambda sigma x ty body =
    let x = Context.annotR (Names.Id.of_string x) in
    EConstr.mkNamedLambda sigma x ty body

  let dprod x ty body =
    let x = Context.nameR (Names.Id.of_string x) in
    EConstr.mkProd (x, ty, body)

  module Logic = struct
    let path = [ "Coq"; "Init"; "Logic" ]

    let eq_ind (mind, i) name =
      Names.(KerName.equal (MutInd.canonical mind) (kername path name)) && i = 0

    let true_ env = mkInd env path "True"
    let false_ env = mkInd env path "False"
    let and_ env f1 f2 = EConstr.mkApp (mkInd env path "and", [| f1; f2 |])
    let or_ env f1 f2 = EConstr.mkApp (mkInd env path "or", [| f1; f2 |])
    let imp f1 f2 = dprod "dummy" f1 f2
    let not env f = EConstr.mkApp (mkConst env path "not", [| f |])
    let iff env f1 f2 = EConstr.mkApp (mkConst env path "iff", [| f1; f2 |])

    let ex env sigma x ty body =
      EConstr.mkApp (mkInd env path "ex", [| ty; lambda sigma x ty body |])

    let fa x ty body = dprod x ty body
    let eq env ty = EConstr.mkApp (mkInd env path "eq", [| ty |])
  end

  module Datatypes = struct
    let path = [ "Coq"; "Init"; "Datatypes" ]

    (* Names. *)

    let nat_name : Names.inductive = (Names.MutInd.make1 (kername path "nat"), 0)
    let zero_name : Names.constructor = (nat_name, 1)
    let succ_name : Names.constructor = (nat_name, 2)

    (* Inductives. *)

    let nat env = mkInd env path "nat"
    let bool env = mkInd env path "bool"
    let unit env = mkInd env path "unit"
    let prod env t1 t2 = EConstr.mkApp (mkInd env path "prod", [| t1; t2 |])
    let option env ty = EConstr.mkApp (mkInd env path "option", [| ty |])
    let list env ty = EConstr.mkApp (mkInd env path "list", [| ty |])

    (* Constructors. *)

    let nil env ty =
      EConstr.mkApp (mkConstruct env path "list" ~constructor:1, [| ty |])

    let cons env ty x l =
      EConstr.mkApp (mkConstruct env path "list" ~constructor:2, [| ty; x; l |])

    let pair env ty1 ty2 t1 t2 =
      EConstr.mkApp
        (mkConstruct env path "prod" ~constructor:1, [| ty1; ty2; t1; t2 |])

    let some env ty t =
      EConstr.mkApp (mkConstruct env path "option" ~constructor:1, [| ty; t |])

    let none env ty =
      EConstr.mkApp (mkConstruct env path "option" ~constructor:2, [| ty |])

    let zero env = mkConstruct env path "nat" ~constructor:1

    let succ env n =
      EConstr.mkApp (mkConstruct env path "nat" ~constructor:2, [| n |])

    let tt env = mkConstruct env path "unit" ~constructor:1

    (* Constructors that depend on ocaml arguments. *)

    let of_bool env b =
      match b with
      | true -> mkConstruct env path "bool" ~constructor:1
      | false -> mkConstruct env path "bool" ~constructor:2

    let rec of_nat env n =
      if n < 0
      then raise @@ Invalid_argument "Trm.Datatypes.of_nat"
      else if n = 0
      then zero env
      else succ env (of_nat env (n - 1))

    let of_list env ty cast l =
      List.fold_right (fun x t -> cons env ty (cast x) t) l (nil env ty)

    let natlist env = of_list env (nat env) (of_nat env)
    let boollist env = of_list env (bool env) (of_bool env)

    let of_option env ty cast opt =
      match opt with None -> none env ty | Some x -> some env ty (cast x)
  end

  module Specif = struct
    let path = [ "Coq"; "Init"; "Specif" ]

    let sigT env sigma x ty p =
      EConstr.mkApp (mkInd env path "sigT", [| ty; lambda sigma x ty p |])

    let existT env sigma x ty p w t =
      EConstr.mkApp
        ( mkConstruct env path "sigT" ~constructor:1
        , [| ty; lambda sigma x ty p; w; t |] )
  end

  let add_knames =
    let modpaths =
      [ [ "Coq"; "Arith"; "PeanoNat"; "Nat" ]; [ "Coq"; "Init"; "Nat" ] ]
    in
    List.map (fun mp -> kername mp "add") modpaths

  let mul_knames =
    let modpaths =
      [ [ "Coq"; "Arith"; "PeanoNat"; "Nat" ]; [ "Coq"; "Init"; "Nat" ] ]
    in
    List.map (fun mp -> kername mp "mul") modpaths

  let add_names : Names.Constant.t list =
    List.map Names.Constant.make1 add_knames

  let mul_names : Names.Constant.t list =
    List.map Names.Constant.make1 mul_knames
end

module Goal = struct
  include Goal

  let hyps_names (goal : Goal.t) = hyps goal |> Context.Named.to_vars

  let fresh_name ?(basename = "H") =
    let base_name = Names.Id.of_string basename in
    fun goal ->
      let hyps_names = hyps_names goal in
      fun () -> Namegen.next_ident_away base_name hyps_names
end
