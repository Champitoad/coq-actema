open Utils.Pervasive
open Api
open CoqUtils

(** The imperative state maintained by the translating algorithm. 
    We could use a state monad instead, but come on this is Ocaml not Haskell. *)
type state =
  { coq_env : Environ.env
  ; sigma : Evd.evar_map
  ; mutable env : Lang.Env.t
        (** The actema environment which contains the constants translated so far. *)
  }

let initial_state coq_goal =
  { coq_env = Goal.env coq_goal
  ; sigma = Goal.sigma coq_goal
  ; env = Lang.Env.empty
  }

let predefined =
  let open Lang in
  [ (Name.dummy, Env.default_pp_info "😬")
  ; (Name.nat, Env.default_pp_info "ℕ")
  ; (Name.and_, Env.{ symbol = "∧"; implicit_args = []; position = Infix })
  ; (Name.or_, Env.{ symbol = "∨"; implicit_args = []; position = Infix })
  ; (Name.not, Env.default_pp_info "¬")
  ; (Name.true_, Env.default_pp_info "⊤")
  ; (Name.false_, Env.default_pp_info "⊥")
  ; (Name.add, Env.{ symbol = "+"; implicit_args = []; position = Infix })
  ; (Name.mul, Env.{ symbol = "⋅"; implicit_args = []; position = Infix })
  ; (Name.eq, Env.{ symbol = "="; implicit_args = [ 0 ]; position = Infix })
  ; (Name.equiv, Env.{ symbol = "↔"; implicit_args = []; position = Infix })
  ]

(** [get_pp_info name] returns the pretty-printing information for [name]. *)
let get_pp_info =
  let open Lang in
  let predefined = Hashtbl.of_seq @@ List.to_seq predefined in
  fun name ->
    match Hashtbl.find_opt predefined name with
    | Some pp -> pp
    | None ->
        (* For an ordinary constant, we simply remove the module path.
           For instance [Coq.Init.Datatypes.nat] is pretty-printed as [nat]. *)
        let parts = String.split_on_char '.' (Name.show name) in
        let symbol = List.nth parts (List.length parts - 1) in
        Env.default_pp_info symbol

(***********************************************************************************)
(** Translate terms. *)

(** Recursively translate a Coq term to an Actema term.
    This is essentially a big match statement. *)
let rec translate_term state (t : EConstr.t) : Lang.Term.t =
  let open Lang in
  if EConstr.isRel state.sigma t
  then
    (* Local variable. *)
    let index = EConstr.destRel state.sigma t in
    Term.mkVar (index - 1)
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
    let binder, ty, body = EConstr.destLambda state.sigma t in
    let name =
      Name.make @@ Pp.string_of_ppcmds @@ Names.Name.print binder.binder_name
    in
    (* Translate the type and body. *)
    let ty = translate_term state ty in
    let body = translate_term state body in
    Term.mkLambda name ty body
  else if EConstr.isProd state.sigma t
  then
    (* Product. *)
    let binder, ty, body = EConstr.destProd state.sigma t in
    (* Translate the type and body. *)
    let ty = translate_term state ty in
    let body = translate_term state body in
    (* Decide whether this is a dependent or non-dependent product.
       For non-dependent products we have to take care to lower the body by [1],
       since we remove the binder. *)
    begin
      match binder.binder_name with
      (* Non-dependent product. *)
      | Anonymous -> Term.mkArrow ty (TermUtils.lift_free (-1) body)
      | _ when not @@ IntSet.mem 0 (TermUtils.free_vars body) ->
          Term.mkArrow ty (TermUtils.lift_free (-1) body)
      (* Dependent product. *)
      | _ ->
          let name =
            Name.make @@ Pp.string_of_ppcmds
            @@ Names.Name.print binder.binder_name
          in
          Term.mkProd name ty body
    end
  else if EConstr.isConst state.sigma t
  then
    (* Constant. *)
    let cname, _ = EConstr.destConst state.sigma t in
    let name = Name.make @@ Names.Constant.to_string cname in
    let cdecl = Environ.lookup_constant cname state.coq_env in
    handle_cst state name @@ EConstr.of_constr cdecl.const_type
  else if EConstr.isVar state.sigma t
  then
    (* Local context variable. *)
    let vname = EConstr.destVar state.sigma t in
    let name = vname |> Names.Id.to_string |> Name.make in
    let ty = type_of_variable state.coq_env vname in
    handle_cst state name ty
  else if EConstr.isConstruct state.sigma t
  then
    (* Constructor. *)
    let cname, _ = EConstr.destConstruct state.sigma t in
    let name =
      kname_of_constructor state.coq_env cname
      |> Names.KerName.to_string |> Name.make
    in
    let ty = type_of_constructor state.coq_env cname in
    handle_cst state name ty
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
    handle_cst state name ty
  else if EConstr.isApp state.sigma t
  then
    (* Application. *)
    let f, args = EConstr.destApp state.sigma t in
    let f = translate_term state f in
    let args = List.map (translate_term state) @@ Array.to_list args in
    Term.mkApps f args
  else
    (* We can't translate [t] : return a dummy constant. *)
    Term.mkCst Name.dummy

(** Constants (i.e. Coq constants, constructors, inductives) need special care. 
    We have to check if we've already seen this constant, and if not 
    we have to translate the constant's type. *)
and handle_cst state (name : Lang.Name.t) (ty : EConstr.t) =
  let open Lang in
  match Name.Map.find_opt name state.env.constants with
  | Some _ -> Term.mkCst name
  | None ->
      (* This is the first time we see this constant : we have to translate its type
         and add the constant to the actema environment. *)
      let ty = translate_term state ty in
      let pp = get_pp_info name in
      state.env <- Env.add_constant name ty ~pp state.env;
      Term.mkCst name

let econstr coq_goal t =
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
    List.fold_left
      begin
        fun (hyps, vars) decl ->
          let name =
            Context.Named.Declaration.get_id decl
            |> Names.Id.to_string |> Lang.Name.make
          in
          let coq_ty =
            decl |> Context.Named.Declaration.get_type |> EConstr.of_constr
          in
          let coq_sort =
            Retyping.get_sort_of state.coq_env state.sigma coq_ty
          in
          let act_ty = translate_term state coq_ty in
          (* Don't forget to add the constant to the actema environment. *)
          let pp = Lang.Env.default_pp_info (Lang.Name.show name) in
          state.env <- Lang.Env.add_constant name act_ty ~pp state.env;
          (* Add it to the list of hypotheses or variables. *)
          if EConstr.ESorts.is_prop state.sigma coq_sort
          then
            (* This is a hypothesis. *)
            let new_hyp = Logic.{ h_name = name; h_gen = 0; h_form = act_ty } in
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
      ([], [])
      (Environ.named_context state.coq_env)
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

(** Split a module path into a directory path and the rest. *)
let rec split_mpath mpath =
  match mpath with
  | Names.ModPath.MPfile dirpath ->
      (List.rev_map Names.Id.to_string (Names.DirPath.repr dirpath), [])
  | Names.ModPath.MPdot (mpath, label) ->
      let dirpath, rest = split_mpath mpath in
      (dirpath, rest @ [ Names.Label.to_string label ])
  | Names.ModPath.MPbound _ ->
      (* Functor arguments are not supported (yet). *)
      raise @@ Invalid_argument "split_mpath"

(** Encode the full name of a lemma. *)
let encode_lemma_name (name : Names.Constant.t) : string option =
  try
    let dirpath, modpath = split_mpath @@ Names.Constant.modpath name in
    let res =
      Format.sprintf "C%s/%s/%s"
        (List.to_string ~sep:"." ~left:"" ~right:"" Fun.id dirpath)
        (List.to_string ~sep:"." ~left:"" ~right:"" Fun.id modpath)
        (Names.Label.to_string @@ Names.Constant.label name)
    in
    Some res
  with Invalid_argument _ -> None

(** Encode the name of an inductive constructor that we want to use as a lemma. *)
let encode_constructor_name (name : Names.Construct.t) : string option =
  try
    let (name, i), j = name in
    let dirpath, modpath = split_mpath @@ Names.MutInd.modpath name in
    let res =
      Format.sprintf "I%s/%s/%s/%d/%d"
        (List.to_string ~sep:"." ~left:"" ~right:"" Fun.id dirpath)
        (List.to_string ~sep:"." ~left:"" ~right:"" Fun.id modpath)
        (Names.Label.to_string @@ Names.MutInd.label name)
        i j
    in
    Some res
  with Invalid_argument _ -> None

(** Collect all the lemmas from coq_env.env_globals.constants we can translate to Actema. *)
let constant_lemmas state : Logic.lemma list =
  let open Lang in
  (Environ.Globals.view state.coq_env.env_globals).constants
  |> Names.Cmap_env.bindings
  |> List.filter_map
       begin
         fun (id, (ckey, _)) ->
           (* First check whether we can encode the lemma name. *)
           match encode_lemma_name id with
           | None -> None
           | Some l_full ->
               let l_user =
                 id |> Names.Constant.label |> Names.Label.to_string
                 |> Name.make
               in
               let ty = ckey.Declarations.const_type |> EConstr.of_constr in
               let l_form = translate_term state ty in
               Some Logic.{ l_user; l_full = Name.make l_full; l_form }
       end

(** Collect all the lemmas from coq_env.env_globals.inductives we can translate to Actema. *)
let constructor_lemmas state : Logic.lemma list =
  let open Lang in
  (* Get the list of all mutual inductives. *)
  (Environ.Globals.view state.coq_env.env_globals).inductives
  |> Names.Mindmap_env.bindings
  (* Get the list of all inductives.
     Inductives in a block are indexed starting at 0. *)
  |> List.concat_map
       begin
         fun (mind_name, (mind_body, _)) ->
           List.init mind_body.Declarations.mind_ntypes @@ fun i ->
           ((mind_name, i), mind_body.Declarations.mind_packets.(i))
       end
  (* Get the list of all inductive constructors (with their type).
     Constructors in an inductive are indexed starting at 1. *)
  |> List.concat_map
       begin
         fun (ind_name, ind_body) ->
           ind_body.Declarations.mind_user_lc |> Array.to_list
           |> List.mapi (fun j ty -> (ind_body, (ind_name, j + 1), ty))
       end
  |> List.filter_map
       begin
         fun (ind_body, cname, ctype) ->
           (* First check whether we can encode the constructor name. *)
           match encode_constructor_name cname with
           | None -> None
           | Some l_full ->
               let _, j = cname in
               let l_user =
                 ind_body.Declarations.mind_consnames.(j - 1)
                 |> Names.Id.to_string |> Name.make
               in
               let l_form = translate_term state @@ EConstr.of_constr ctype in
               Some Logic.{ l_user; l_full = Name.make l_full; l_form }
       end

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
          let form = l.Logic.l_form in
          (* Check we managed to translate all the lemma's subterms. *)
          (not (Name.Set.mem Name.dummy (TermUtils.constants form)))
          (* Check the lemma type-checks. This can sometimes fail because Coq
             uses beta-conversion when type-checking, but Actema does not. *)
          && Typing.well_typed state.env form
      end
      (l1 @ l2)
  in
  (lemmas, state.env)
