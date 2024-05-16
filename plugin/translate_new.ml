open Api_new
open CoqUtils

(** The imperative state maintained by the translating algorithm. 
    We could use a state monad instead, but come on this is Ocaml not Haskell. *)
type state =
  { coq_env : Environ.env
  ; sigma : Evd.evar_map
  ; mutable env : Lang.Env.t
        (** The actema environment which contains the constants translated so far. *)
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

(** Recursively translate a Coq term to an Actema term.*)
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
    match binder.binder_name with
    | Anonymous ->
        (* Non-dependent product. *)
        (* Translate the type and body. *)
        let ty = translate_term state ty in
        let body = translate_term state body in
        Term.mkArrow ty body
    | Name _ ->
        (* Dependent product. *)
        let name =
          Name.make @@ Pp.string_of_ppcmds
          @@ Names.Name.print binder.binder_name
        in
        (* Translate the type and body. *)
        let ty = translate_term state ty in
        let body = translate_term state body in
        Term.mkProd name ty body
  else if EConstr.isConst state.sigma t
  then begin
    (* Constant. *)
    let cname, _ = EConstr.destConst state.sigma t in
    let name = Name.make @@ Names.Constant.to_string cname in
    let cdecl = Environ.lookup_constant cname state.coq_env in
    handle_cst state name @@ EConstr.of_constr cdecl.const_type
  end
  else if EConstr.isConstruct state.sigma t
  then begin
    (* Constructor. *)
    let cname, _ = EConstr.destConstruct state.sigma t in
    let name =
      kname_of_constructor state.coq_env cname
      |> Names.KerName.to_string |> Name.make
    in
    let ty = type_of_constructor state.coq_env cname in
    handle_cst state name ty
  end
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

let translate_goal coq_goal : Logic.pregoal =
  (* Create an initial state. *)
  let state =
    { coq_env = Goal.env coq_goal
    ; sigma = Goal.sigma coq_goal
    ; env = Lang.Env.empty
    }
  in
  (* Translate the conclusion. *)
  let concl = translate_term state (Goal.concl coq_goal) in
  (* Translate the hypotheses and variables. *)
  let hyps =
    List.filter_map
      begin
        fun decl ->
          let name =
            Context.Named.Declaration.get_id decl
            |> Names.Id.to_string |> Lang.Name.make
          in
          let ty =
            decl |> Context.Named.Declaration.get_type |> EConstr.of_constr
          in
          let sort = Retyping.get_sort_of state.coq_env state.sigma ty in
          let ty = translate_term state ty in
          (* Don't forget to add the constant to the actema environment. *)
          let pp = Lang.Env.default_pp_info (Lang.Name.show name) in
          state.env <- Lang.Env.add_constant name ty ~pp state.env;
          (* If this is a hypothesis, add it to the list. *)
          if EConstr.ESorts.is_prop state.sigma sort
          then
            (* This is a hypothesis. *)
            Some Logic.{ h_src = Some name; h_gen = 0; h_form = ty }
          else (* This is a variable. *)
            None
      end
      (Environ.named_context state.coq_env)
  in
  (* Construct the actema pregoal. *)
  Logic.{ g_env = state.env; g_hyps = hyps; g_goal = concl }
