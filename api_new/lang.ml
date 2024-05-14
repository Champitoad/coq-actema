(***************************************************************************************)
(** Names *)

module Name = struct
  type t = { str : string; hsh : int } [@@deriving show]

  let show name = name.str
  let pp fmt name = Format.fprintf fmt "%s" name.str

  (** We compute the hash of [str] once and forall, and reuse it later. *)
  let make str = { str; hsh = Hashtbl.hash str }

  let hash name = name.hsh
  let equal n1 n2 = n1.hsh = n2.hsh && n1.str = n2.str
  let compare n1 n2 = compare n1 n2

  module Set = Set.Make (struct
    type nonrec t = t

    let compare = compare
  end)

  module Map = Map.Make (struct
    type nonrec t = t

    let compare = compare
  end)

  module Hashtbl = Hashtbl.Make (struct
    type nonrec t = t

    let hash = hash
    let equal = equal
  end)

  (** We use a special symbol [!] to ensure this is distinct from any Coq identifiers. *)
  let dummy = make "!dummy"

  let and_ = make "Coq.Init.Logic.and"
  let or_ = make "Coq.Init.Logic.or"
end

(***************************************************************************************)
(** Terms *)

module Term = struct
  type t =
    | Var of Name.t
    | App of t * t list
    | Lambda of Name.t * t * t
    | Arrow of t * t
    | Prod of Name.t * t * t
    | Cst of Name.t
    | Sort of [ `Prop | `Type ]
  [@@deriving show]

  let mkVar name = Var name

  let mkApp f arg =
    match f with
    | App (f, f_args) -> App (f, f_args @ [ arg ])
    | _ -> App (f, [ arg ])

  let mkApps f args =
    assert (not @@ List.is_empty args);
    match f with App (f, f_args) -> App (f, f_args @ args) | _ -> App (f, args)

  let mkLambda name ty body = Lambda (name, ty, body)
  let mkArrow t1 t2 = Arrow (t1, t2)

  let mkArrows ts =
    match List.rev ts with
    | [] -> failwith "Term.mkArrows : got an empty list."
    | t :: ts -> List.fold_right mkArrow (List.rev ts) t

  let mkProd name ty body = Prod (name, ty, body)
  let mkCst name = Cst name
  let mkProp = Sort `Prop
  let mkType = Sort `Type
  let mkSort s = Sort s
end

(***************************************************************************************)
(** Environments *)

module Env = struct
  type pp_info = { symbol : string; position : [ `Prefix | `Infix | `Suffix ] }
  [@@deriving show]

  type t = { constants : Term.t Name.Map.t; pp_info : pp_info Name.Map.t }

  let empty = { constants = Name.Map.empty; pp_info = Name.Map.empty }

  let add_constant name ty env =
    { env with constants = Name.Map.add name ty env.constants }
end

(***************************************************************************************)
(** Term utility functions. *)

module TermUtils = struct
  (** [acc] is the list of free variables already found. 
      [bound] is the list of variables bound above [t]. *)
  let rec free_vars_rec (acc : Name.t list) (bound : Name.t list) (t : Term.t) :
      Name.t list =
    match (t : Term.t) with
    | Var v -> if List.mem v bound then acc else v :: acc
    | Cst _ | Sort _ -> acc
    | App (f, args) ->
        List.fold_left (fun acc t -> free_vars_rec acc bound t) acc (f :: args)
    | Arrow (t1, t2) ->
        let acc = free_vars_rec acc bound t1 in
        let acc = free_vars_rec acc bound t2 in
        acc
    | Lambda (x, ty, body) | Prod (x, ty, body) ->
        let acc = free_vars_rec acc bound ty in
        let acc = free_vars_rec acc (x :: bound) body in
        acc

  let free_vars t = Name.Set.of_list @@ free_vars_rec [] [] t

  let rec subst name u t =
    match (t : Term.t) with
    | Var v -> if Name.equal v name then u else Term.mkVar v
    | Cst _ | Sort _ -> t
    | App (f, args) ->
        Term.mkApps (subst name u f) (List.map (subst name u) args)
    | Lambda (x, ty, body) ->
        if Name.equal name x
        then Term.mkLambda x (subst name u ty) body
        else Term.mkLambda x (subst name u ty) (subst name u body)
    | Prod (x, ty, body) ->
        if Name.equal name x
        then Term.mkProd x (subst name u ty) body
        else Term.mkProd x (subst name u ty) (subst name u body)
    | Arrow (a, b) -> Term.mkArrow (subst name u a) (subst name u b)
end

(***************************************************************************************)
(** Typing. *)

module Typing = struct
  (** See the error messages in [pp_typeError] for an explanation of 
      the different error cases. *)
  type typeError =
    | UnknownVar of Name.t
    | UnknownCst of Name.t
    | ExpectedType of Term.t * Term.t * Term.t
    | ExpectedFunction of Term.t * Term.t
    | ExpectedSort of Term.t * Term.t

  let pp_typeError fmt err =
    match err with
    | UnknownVar v -> Format.fprintf fmt "Unbound variable\n%a" Name.pp v
    | UnknownCst c -> Format.fprintf fmt "Unbound constant\n%a" Name.pp c
    | ExpectedType (term, actual_ty, expected_ty) ->
        Format.fprintf fmt
          "The term\n%a\nhas type\n%a\nbut a term of type\n%a\nwas expected"
          Term.pp term Term.pp actual_ty Term.pp expected_ty
    | ExpectedFunction (term, ty) ->
        Format.fprintf fmt
          "The term\n%a\nhas type\n%a\nbut a function type was expected" Term.pp
          term Term.pp ty
    | ExpectedSort (term, ty) ->
        Format.fprintf fmt
          "The term\n%a\nhas type\n%a\nbut a sort (Type or Prop) was expected"
          Term.pp term Term.pp ty

  let show_typeError err = Format.asprintf "%a" pp_typeError err

  exception TypingError of typeError

  (** There is no need for unification here :
      all binders are annotated with the type of the bound variable. *)
  let rec check_rec env vars t : Term.t =
    match (t : Term.t) with
    | Var v -> begin
        match List.assoc_opt v vars with
        | None -> raise @@ TypingError (UnknownVar v)
        | Some ty -> ty
      end
    | Cst c -> begin
        match Name.Map.find_opt c env.Env.constants with
        | None -> raise @@ TypingError (UnknownCst c)
        | Some ty -> ty
      end
    | Sort _ -> Sort `Type
    | Lambda (v, ty, body) ->
        let _ = check_rec env vars ty in
        let body_ty = check_rec env ((v, ty) :: vars) body in
        (* Depending on whether [v] appears in [body_ty],
           this is a dependent or non-dependent product. *)
        if Name.Set.mem v (TermUtils.free_vars body_ty)
        then Term.mkProd v ty body_ty
        else Term.mkArrow ty body_ty
    | App (f, args) ->
        let _res, res_ty =
          List.fold_left (check_app env vars) (f, check_rec env vars f) args
        in
        res_ty
    | Arrow (a, b) -> begin
        let a_ty = check_rec env vars a in
        let b_ty = check_rec env vars b in
        match (a_ty, b_ty) with
        | Sort _, Sort _ -> b_ty
        | Sort _, _ -> raise @@ TypingError (ExpectedSort (b, b_ty))
        | _, _ -> raise @@ TypingError (ExpectedSort (a, a_ty))
      end
    | Prod (x, a, b) -> begin
        let a_ty = check_rec env vars a in
        let b_ty = check_rec env ((x, a) :: vars) b in
        match (a_ty, b_ty) with
        | Sort _, Sort _ -> b_ty
        | Sort _, _ -> raise @@ TypingError (ExpectedSort (b, b_ty))
        | _, _ -> raise @@ TypingError (ExpectedSort (a, a_ty))
      end

  (** Type-check an application with a single argument. 
      It takes as argument (and returns) a pair [term, type_]. *)
  and check_app env vars (f, f_ty) arg =
    let arg_ty = check_rec env vars arg in
    match f_ty with
    | Arrow (a, b) ->
        if arg_ty = a
        then (Term.mkApp f arg, b)
        else raise @@ TypingError (ExpectedType (arg, arg_ty, a))
    | Prod (x, a, b) ->
        if arg_ty = a
        then (Term.mkApp f arg, TermUtils.subst x arg b)
        else raise @@ TypingError (ExpectedType (arg, arg_ty, a))
    | _ -> raise @@ TypingError (ExpectedFunction (f, f_ty))

  let check env t = check_rec env [] t
  let typeof env t = failwith "TODO"
end

module TermGen = struct
  open QCheck2

  let ( let* ) = Gen.bind
  let gen_letter = Gen.(Char.chr <$> oneof [ 65 -- 90; 97 -- 122 ])

  let gen_name : Name.t Gen.t =
    Gen.(map Name.make @@ string_size ~gen:gen_letter (1 -- 5))

  let split_nat n : (int * int) Gen.t =
    assert (n >= 0);
    let* k = Gen.(0 -- n) in
    Gen.return (k, n - k)

  (** Generate a term with exactly [n] interior nodes 
      (i.e. not counting variables, constants or sorts). *)
  let rec simple_sized n : Term.t Gen.t =
    let open Gen in
    let open Term in
    if n <= 0
    then
      oneof
        [ mkVar <$> gen_name
        ; mkCst <$> gen_name
        ; Gen.return mkProp
        ; Gen.return mkType
        ]
    else
      let* n1, n2 = split_nat (n - 1) in
      oneof
        [ mkLambda <$> gen_name <*> simple_sized n1 <*> simple_sized n2
        ; mkProd <$> gen_name <*> simple_sized n1 <*> simple_sized n2
        ; mkArrow <$> simple_sized n1 <*> simple_sized n2
        ; mkApp <$> simple_sized n1 <*> simple_sized n2
        ]

  let simple : Term.t Gen.t = Gen.sized simple_sized

  (*let rec scoped_sized env bound n : Term.t option Gen.t =
    let open Gen in
    let open Term in
    if n <= 0
    then
      (* Generate a leaf term. *)
      let gen_var =
        if bound = []
        then return None
        else
          let+ b = oneofl bound in
          Some (mkVar b)
      in
      let gen_cst =
        let+ name, _ = oneofl (Name.Map.bindings env.Env.constants) in
        Some (mkCst name)
      in
      frequency
        [ (5, gen_var)
        ; (5, gen_cst)
        ; (1, Gen.return @@ Some mkProp)
        ; (1, Gen.return @@ Some mkType)
        ]
    else
      (* Generate a term with children. *)
      let* n1, n2 = split_nat (n - 1) in
      let gen_lambda =
        let* x = gen_name in
        mkLambda x <$> scoped_sized env bound n1
        <*> scoped_sized env (x :: bound) n2
      in
      let gen_prod =
        let* x = gen_name in
        mkProd x <$> scoped_sized env bound n1
        <*> scoped_sized env (x :: bound) n2
      in
      let gen_arrow =
        mkArrow <$> scoped_sized env bound n1 <*> scoped_sized env bound n2
      in
      let gen_app =
        mkApp <$> scoped_sized env bound n1 <*> scoped_sized env bound n2
      in
      frequency [ (1, gen_lambda); (1, gen_prod); (1, gen_arrow); (4, gen_app) ]*)

  let scoped env = Gen.sized @@ scoped_sized env []

  let typed_sized env vars ty n : Term.t Gen.t =
    let open Gen in
    let open Term in
    if n <= 0 then oneof [ mkVar <$> oneofl vars ] else failwith "todo"

  let typed env =
    (* First choose a random (not too complex) type. *)
    let ty = failwith "todo" in
    (* Generate a term with this type. *)
    Gen.sized @@ typed_sized env [] ty
end
