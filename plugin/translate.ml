open Utils.Pervasive
open Api
open CoqUtils
module Bimap = Utils.Bimap

(***********************************************************************************)
(** Translate Coq to Actema. *)

module Export = struct
  exception CannotTranslate of EConstr.t

  (** The imperative state maintained by the translating algorithm. 
      We could use a state monad instead, but come on this is Ocaml not Haskell. *)
  type state =
    { (* Coq's environment. *)
      coq_env : Environ.env
    ; (* Coq's unification state. *) sigma : Evd.evar_map
    ; (* The actema environment which contains the constants translated so far. *)
      mutable env : Lang.Env.t
    }

  let initial_state coq_goal =
    { coq_env = Goal.env coq_goal
    ; sigma = Goal.sigma coq_goal
    ; env = Lang.Env.empty
    }

  (** We manually set pretty-printing information for specific Coq terms. *)
  let predefined =
    let open Lang in
    let open Precedence in
    [ ( Constants.nat
      , Env.
          { symbol = "ℕ"
          ; implicit_args = []
          ; position = Prefix
          ; precedence = NeverParen
          } )
    ; ( Constants.and_
      , Env.
          { symbol = "∧"
          ; implicit_args = []
          ; position = Infix
          ; precedence = Level 80
          } )
    ; ( Constants.or_
      , Env.
          { symbol = "∨"
          ; implicit_args = []
          ; position = Infix
          ; precedence = Level 85
          } )
    ; ( Constants.not
      , Env.
          { symbol = "¬"
          ; implicit_args = []
          ; position = Infix
          ; precedence = Level 75
          } )
    ; ( Constants.true_
      , Env.
          { symbol = "⊤"
          ; implicit_args = []
          ; position = Infix
          ; precedence = NeverParen
          } )
    ; ( Constants.false_
      , Env.
          { symbol = "⊥"
          ; implicit_args = []
          ; position = Infix
          ; precedence = NeverParen
          } )
    ; ( Constants.add
      , Env.
          { symbol = "+"
          ; implicit_args = []
          ; position = Infix
          ; precedence = Level 50
          } )
    ; ( Constants.mul
      , Env.
          { symbol = "⋅"
          ; implicit_args = []
          ; position = Infix
          ; precedence = Level 40
          } )
    ; ( Constants.eq
      , Env.
          { symbol = "="
          ; implicit_args = [ 0 ]
          ; position = Infix
          ; precedence = Level 70
          } )
    ; ( Constants.equiv
      , Env.
          { symbol = "↔"
          ; implicit_args = []
          ; position = Infix
          ; precedence = Level 95
          } )
    ; ( Constants.nil
      , Env.
          { symbol = "[]"
          ; implicit_args = [ 0 ]
          ; position = Prefix
          ; precedence = NeverParen
          } )
    ; ( Constants.cons
      , Env.
          { symbol = "::"
          ; implicit_args = [ 0 ]
          ; position = Infix
          ; precedence = Level 60
          } )
    ]
    |> List.to_seq |> Hashtbl.of_seq

  (** Translate implicit arguments from Coq format to Actema format.
      We are a bit more strict than Coq as to which arguments are considered implicit. *)
  let compute_implicits implicits : int list =
    let open Impargs in
    let for_one info : int option =
      match info.impl_expl with
      | DepRigid _ | Manual ->
          let _, i, _ = info.Impargs.impl_pos in
          (* Coq indexes arguments starting at 1 but Actema starts at 0. *)
          Some (i - 1)
      | _ -> None
    in
    implicits
    |> List.filter_map (function Some info -> for_one info | None -> None)
    |> List.sort Int.compare

  (** [make_pp_info name ref] creates the pretty-printing information for [name]. *)
  let make_pp_info name ref =
    let open Lang in
    match Hashtbl.find_opt predefined name with
    (* We handle this constant in a special way. *)
    | Some pp -> pp
    (* Just an ordinary constant. *)
    | None ->
        (* We don't print the module path.
           For instance [Coq.Init.Datatypes.nat] is pretty-printed as [nat]. *)
        let parts = String.split_on_char '.' (Name.show name) in
        let symbol = List.nth parts (List.length parts - 1) in
        (* Compute implicit arguments. *)
        let implicit_args =
          match Impargs.implicits_of_global ref with
          | [ (_, implicits) ] -> compute_implicits implicits
          (* Some constants have more than one list of implicit arguments.
             I have no idea what this corresponds to : in this case we mark all arguments
             as explicit. *)
          | _ -> []
        in
        (* By default a constant is printed in prefix position and binds tightly. *)
        Env.{ symbol; implicit_args; position = Prefix; precedence = Level 0 }

  (***********************************************************************************)
  (** Translate terms. *)

  (** Recursively translate a Coq term to an Actema term.
      This is essentially a big match statement. 
    
      Here we don't bother with FVars : we directly construct BVars. 
      This means intermediate results may contain loose bound variables. *)
  let rec translate_term state (t : EConstr.t) : Lang.Term.t =
    let open Lang in
    if EConstr.isRel state.sigma t
    then
      (* Local variable. BEWARE : Coq starts de Bruijn indices at 1. *)
      let index = EConstr.destRel state.sigma t in
      Term.mkBVar (index - 1)
    else if EConstr.isSort state.sigma t
    then
      (* Sorts. *)
      let sort = EConstr.destSort state.sigma t in
      if EConstr.ESorts.is_prop state.sigma sort
      then Term.mkProp
      else
        (* Everything that is not a Prop is translated to Type.
           We do loose some information here. *)
        Term.mkType
    else if EConstr.isLambda state.sigma t
    then
      (* Lambda abstraction. *)
      let coq_binder, ty, body = EConstr.destLambda state.sigma t in
      let binder =
        match coq_binder.binder_name with
        | Anonymous -> Term.Anonymous
        | Name name -> Term.Named (Name.make @@ Names.Id.to_string name)
      in
      (* Translate the type and body. *)
      let ty = translate_term state ty in
      let body = translate_term state body in
      Term.mkLambda binder ty body
    else if EConstr.isProd state.sigma t
    then
      (* Product. *)
      let coq_binder, ty, body = EConstr.destProd state.sigma t in
      (* Translate the type and body. *)
      let ty = translate_term state ty in
      let body = translate_term state body in
      let binder =
        match coq_binder.binder_name with
        | Anonymous -> Term.Anonymous
        | Name name -> Term.Named (Name.make @@ Names.Id.to_string name)
      in
      Term.mkProd binder ty body
    else if EConstr.isConst state.sigma t
    then
      (* Constant. *)
      let cname, _ = EConstr.destConst state.sigma t in
      let name = Name.make @@ Names.Constant.to_string cname in
      let cdecl = Environ.lookup_constant cname state.coq_env in
      handle_cst state name
        (EConstr.of_constr cdecl.const_type)
        (Names.GlobRef.ConstRef cname)
    else if EConstr.isVar state.sigma t
    then
      (* Local context variable. *)
      let vname = EConstr.destVar state.sigma t in
      let name = vname |> Names.Id.to_string |> Name.make in
      let ty = type_of_variable state.coq_env vname in
      handle_cst state name ty (Names.GlobRef.VarRef vname)
    else if EConstr.isConstruct state.sigma t
    then
      (* Constructor. *)
      let cname, _ = EConstr.destConstruct state.sigma t in
      let name =
        kname_of_constructor state.coq_env cname
        |> Names.KerName.to_string |> Name.make
      in
      let ty = type_of_constructor state.coq_env cname in
      handle_cst state name ty (Names.GlobRef.ConstructRef cname)
    else if EConstr.isInd state.sigma t
    then
      (* Inductive. *)
      let iname, _ = EConstr.destInd state.sigma t in
      let modpath = Names.Ind.modpath iname in
      let body = ind_body state.coq_env iname in
      let name =
        Name.make
          (Names.ModPath.to_string modpath
          ^ "."
          ^ Names.Id.to_string body.mind_typename)
      in
      let ty = Retyping.get_type_of state.coq_env state.sigma t in
      handle_cst state name ty (Names.GlobRef.IndRef iname)
    else if EConstr.isApp state.sigma t
    then
      (* Application. *)
      let f, args = EConstr.destApp state.sigma t in
      let f = translate_term state f in
      let args = List.map (translate_term state) @@ Array.to_list args in
      Term.mkApps f args
    else
      (* We can't translate [t] : raise an exception. *)
      raise @@ CannotTranslate t

  (** Constants (i.e. Coq constants, constructors, inductives) need special care. 
      We have to check if we've already seen this constant, and if not 
      we have to translate the constant's type. *)
  and handle_cst state name (ty : EConstr.t) (ref : Names.GlobRef.t) =
    let open Lang in
    match Name.Map.find_opt name state.env.constants with
    | Some _ -> Term.mkCst name
    | None ->
        (* This is the first time we see this constant : we have to translate its type
           and add the constant to the actema environment. *)
        let ty = translate_term state ty in
        let pp = make_pp_info name ref in
        state.env <- Env.add_constant name ty ~pp state.env;
        Term.mkCst name

  let econstr coq_goal t : Lang.Term.t * Lang.Env.t =
    (* Create an initial state. *)
    let state = initial_state coq_goal in
    (* Translate the term. *)
    let res = translate_term state t in
    (res, state.env)

  (***********************************************************************************)
  (** Translate goals. *)

  let goal coq_goal : Logic.pregoal =
    (* Create an initial state. *)
    let state = initial_state coq_goal in
    (* Translate the conclusion. *)
    let concl = translate_term state (Goal.concl coq_goal) in
    (* Translate the hypotheses and variables. *)
    let hyps, vars =
      fold_context
        begin
          fun decl (hyps, vars) ->
            let name =
              Context.Named.Declaration.get_id decl
              |> Names.Id.to_string |> Name.make
            in
            let coq_ty =
              decl |> Context.Named.Declaration.get_type |> EConstr.of_constr
            in
            let coq_sort =
              Retyping.get_sort_of state.coq_env state.sigma coq_ty
            in
            let act_ty = translate_term state coq_ty in
            (* Don't forget to add the constant to the actema environment. *)
            let pp =
              make_pp_info name
              @@ Names.GlobRef.VarRef (Context.Named.Declaration.get_id decl)
            in
            state.env <- Lang.Env.add_constant name act_ty ~pp state.env;
            (* Add it to the list of hypotheses or variables. *)
            if EConstr.ESorts.is_prop state.sigma coq_sort
            then
              (* This is a hypothesis. *)
              let new_hyp =
                Logic.{ h_name = name; h_gen = 0; h_form = act_ty }
              in
              (new_hyp :: hyps, vars)
            else
              (* This is a variable. *)
              (* Get the body of the variable and translate it (if it exists). *)
              let coq_body = Context.Named.Declaration.get_value decl in
              let act_body =
                Option.map (translate_term state <<< EConstr.of_constr) coq_body
              in
              let new_var =
                Logic.{ v_name = name; v_type = act_ty; v_body = act_body }
              in
              (hyps, new_var :: vars)
        end
        state.coq_env ([], [])
    in
    (* Construct the actema pregoal. *)
    Logic.
      { g_env = state.env
      ; g_vars = Vars.of_list vars
      ; g_hyps = Hyps.of_list hyps
      ; g_concl = concl
      }

  (***********************************************************************************)
  (** Translate lemmas. *)

  (** Compute the user name associated to a lemma. 
      Currently we simply discard the module path, but this could change in the future. *)
  let lemma_user_name l_full : Name.t =
    let raw = Name.show l_full in
    let segments = String.split_on_char '.' raw in
    Name.make @@ List.last segments

  (** Collect constant lemmas. *)
  let constant_lemmas state : Logic.lemma list =
    Environ.fold_constants
      begin
        fun cname cbody lemmas ->
          try
            let l_full = cname |> Names.Constant.to_string |> Name.make in
            let l_user = lemma_user_name l_full in
            let l_form =
              translate_term state @@ EConstr.of_constr cbody.const_type
            in
            Logic.{ l_user; l_full; l_form } :: lemmas
          with CannotTranslate _ -> lemmas
      end
      state.coq_env []

  (** Collect constructor lemmas. *)
  let constructor_lemmas state : Logic.lemma list =
    fold_constructors
      begin
        fun ctr_name ctr_type lemmas ->
          try
            let l_full =
              kname_of_constructor state.coq_env ctr_name
              |> Names.KerName.to_string |> Name.make
            in
            let l_user = lemma_user_name l_full in
            let l_form = translate_term state @@ EConstr.of_constr ctr_type in
            Logic.{ l_user; l_full; l_form } :: lemmas
          with CannotTranslate _ -> lemmas
      end
      state.coq_env []

  let lemmas coq_goal : Logic.lemma list * Lang.Env.t =
    let open Lang in
    let state = initial_state coq_goal in
    let l1 = constant_lemmas state in
    let l2 = constructor_lemmas state in

    (* Filter out the lemmas that we couldn't translate correctly. *)
    let lemmas =
      List.filter
        begin
          fun l ->
            (* Check the lemma type-checks. This can sometimes fail because Coq
               uses beta-conversion when type-checking, but Actema does not. *)
            TermUtils.well_typed state.env Context.empty l.Logic.l_form
        end
        (l1 @ l2)
    in
    (lemmas, state.env)
end

(***********************************************************************************)
(** Symbols. *)

module Symbols = struct
  type symbol =
    | SCst of Names.Constant.t
    | SCtr of Names.Construct.t
    | SInd of Names.Ind.t
    | SVar of Names.Id.t

  module Table =
    Bimap.Make
      (Name)
      (struct
        type t = symbol

        let compare = Stdlib.compare
      end)

  let extract_constants coq_goal table : Table.t =
    Environ.fold_constants
      begin
        fun c_name _ table ->
          let name = c_name |> Names.Constant.to_string |> Name.make in
          Table.add name (SCst c_name) table
      end
      (Goal.env coq_goal) table

  let extract_inductives coq_goal table : Table.t =
    fold_inductives
      begin
        fun i_name _ table ->
          let name =
            kname_of_inductive (Goal.env coq_goal) i_name
            |> Names.KerName.to_string |> Name.make
          in
          Table.add name (SInd i_name) table
      end
      (Goal.env coq_goal) table

  let extract_constructors coq_goal table : Table.t =
    fold_constructors
      begin
        fun ctr_name _ table ->
          let name =
            kname_of_constructor (Goal.env coq_goal) ctr_name
            |> Names.KerName.to_string |> Name.make
          in
          Table.add name (SCtr ctr_name) table
      end
      (Goal.env coq_goal) table

  let extract_context coq_goal table : Table.t =
    fold_context
      begin
        fun decl table ->
          match decl with
          | LocalAssum (binder, _) | LocalDef (binder, _, _) ->
              let name = Name.make @@ Names.Id.to_string binder.binder_name in
              Table.add name (SVar binder.binder_name) table
      end
      (Goal.env coq_goal) table

  let globals coq_goal =
    Table.empty
    |> extract_constructors coq_goal
    |> extract_inductives coq_goal
    |> extract_constants coq_goal

  let locals coq_goal = Table.empty |> extract_context coq_goal

  let all coq_goal =
    Table.empty
    |> extract_constructors coq_goal
    |> extract_inductives coq_goal
    |> extract_constants coq_goal |> extract_context coq_goal

  let to_econstr coq_goal symbol =
    match symbol with
    | SCst cname ->
        let (_, inst), _ =
          UnivGen.fresh_constant_instance (Goal.env coq_goal) cname
        in
        EConstr.mkConstU (cname, EConstr.EInstance.make inst)
    | SCtr cname ->
        let (_, inst), _ =
          UnivGen.fresh_constructor_instance (Goal.env coq_goal) cname
        in
        EConstr.mkConstructU (cname, EConstr.EInstance.make inst)
    | SInd iname ->
        let (_, inst), _ =
          UnivGen.fresh_inductive_instance (Goal.env coq_goal) iname
        in
        EConstr.mkIndU (iname, EConstr.EInstance.make inst)
    | SVar vname -> EConstr.mkVar vname
end

(***********************************************************************************)
(** Translate Actema to Coq. *)

module Import = struct
  type state = { coq_goal : Goal.t; table : Symbols.Table.t }

  let translate_binder (binder : Lang.Term.binder) :
      Names.Name.t Context.binder_annot =
    let str =
      match binder with Named name -> Name.show name | Anonymous -> "_"
    in
    let name = Names.Name.mk_name @@ Names.Id.of_string str in
    { binder_name = name; binder_relevance = Relevant }

  (** This assumes the input term contains no FVar and no loose BVar. *)
  let rec translate_term state (term : Lang.Term.t) : EConstr.t =
    match term with
    | BVar idx ->
        (* Take care that Coq starts de Bruijn indices at 1, while Actema starts at 0. *)
        EConstr.mkRel (idx + 1)
    | FVar _ -> failwith "Import.translate_term : unexpected free variable."
    | Cst name -> begin
        match Symbols.Table.find_opt name state.table with
        | Some symbol -> Symbols.to_econstr state.coq_goal symbol
        | None ->
            failwith
            @@ Format.sprintf
                 "Import.translate_term : could not find symbol for [%s]"
                 (Name.show name)
      end
    | Sort `Prop -> EConstr.mkProp
    | Sort `Type ->
        let level = UnivGen.fresh_level () in
        EConstr.mkType @@ Univ.Universe.make level
    | Lambda (_, x, ty, body) ->
        let binder = translate_binder x in
        let ty = translate_term state ty in
        let body = translate_term state body in
        EConstr.mkLambda (binder, ty, body)
    | Prod (_, x, ty, body) ->
        let binder = translate_binder x in
        let ty = translate_term state ty in
        let body = translate_term state body in
        EConstr.mkProd (binder, ty, body)
    | App (_, f, args) ->
        let f = translate_term state f in
        let args = List.map (translate_term state) args in
        EConstr.mkApp (f, Array.of_list args)

  let term coq_goal table term : EConstr.t =
    let state = { coq_goal; table } in
    translate_term state term
end
