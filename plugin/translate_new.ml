open Api_new
open Lang

(** The imperative state maintained by the translating algorithm. 
    We could use a state monad instead, but come on this is Ocaml not Haskell. *)
type state =
  { coq_env : Environ.env
  ; sigma : Evd.evar_map
  ; mutable env : Env.t
        (** The actema environment which contains the constants translated so far. *)
  }

(** Recursively translate a Coq term to an Actema term.*)
let rec translate_term state (t : EConstr.t) : Term.t =
  if EConstr.isRel state.sigma t (* Local variable. *)
  then
    let index = EConstr.destRel state.sigma t in
    Term.mkVar (index - 1)
  else if EConstr.isLambda state.sigma t
  then
    (* Lambda abstraction. *)
    let binder, ty, body = EConstr.destLambda state.sigma t in
    let name =
      Name.make @@ Pp.string_of_ppcmds @@ Names.Name.print binder.binder_name
    in
    (* Translate the type and body. Don't forget to add [name] to [vars]. *)
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
    if Name.Map.mem name state.env.constants
    then Term.mkCst name
    else
      (* This is the first time we see this constant : we have to translate its type
         and add the constant to the actema environment. *)
      let cdecl = Environ.lookup_constant cname state.coq_env in
      let ty = translate_term state @@ EConstr.of_constr cdecl.const_type in
      state.env <- Env.add_constant name ty state.env;
      Term.mkCst name
  end
  else
    (* We can't translate [t] : return a dummy constant. *)
    Term.mkCst Name.dummy
