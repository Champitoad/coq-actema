open Utils

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

  let test_env =
    let open Term in
    let nat = mkCst @@ Name.make "nat" in
    let constants =
      [ ("True", mkProp)
      ; ("False", mkProp)
      ; ("or", mkArrows [ mkProp; mkProp; mkProp ])
      ; ("and", mkArrows [ mkProp; mkProp; mkProp ])
      ; ("not", mkArrow mkProp mkProp)
      ; ("nat", mkType)
      ; ("Zero", nat)
      ; ("Succ", mkArrow nat nat)
      ; ("plus", mkArrows [ nat; nat; nat ])
      ; ("mult", mkArrows [ nat; nat; nat ])
      ; ("le", mkArrows [ nat; nat; mkProp ])
      ]
    in
    List.fold_left
      (fun env (name, ty) -> add_constant (Name.make name) ty env)
      empty constants
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
    | UnknownVar v -> Format.fprintf fmt "Unbound variable\n%s" (Name.show v)
    | UnknownCst c -> Format.fprintf fmt "Unbound constant\n%s" (Name.show c)
    | ExpectedType (term, actual_ty, expected_ty) ->
        Format.fprintf fmt
          "The term\n%s\nhas type\n%s\nbut a term of type\n%s\nwas expected"
          (Term.show term) (Term.show actual_ty) (Term.show expected_ty)
    | ExpectedFunction (term, ty) ->
        Format.fprintf fmt
          "The term\n%s\nhas type\n%s\nbut a function type was expected"
          (Term.show term) (Term.show ty)
    | ExpectedSort (term, ty) ->
        Format.fprintf fmt
          "The term\n%s\nhas type\n%s\nbut a sort (Type or Prop) was expected"
          (Term.show term) (Term.show ty)

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

  let check ?(context = []) env t = check_rec env context t
  let typeof ?context env t = failwith "TODO"
end

(***************************************************************************************)
(** Random term generation. *)

module TermGen = struct
  open QCheck2
  open BGen.Syntax

  let gen_letter = Gen.(Char.chr <$> oneof [ 65 -- 90; 97 -- 122 ])

  (** We choose small names so that collisions are more likely. *)
  let gen_name : Name.t Gen.t =
    Gen.(map Name.make @@ string_size ~gen:gen_letter (1 -- 3))

  let gen_sort : Term.t Gen.t = Gen.oneofl [ Term.mkProp; Term.mkType ]

  let split_nat n : (int * int) Gen.t =
    assert (n >= 0);
    Gen.(0 -- n >|= fun k -> (k, n - k))

  let split_list_at n xs =
    let rec loop n acc xs =
      match xs with
      | _ when n <= 0 -> (List.rev acc, xs)
      | [] -> (List.rev acc, xs)
      | x :: xs -> loop (n - 1) (x :: acc) xs
    in
    loop n [] xs

  (*************************************************************************************)
  (** Simple term generation. *)

  (** We use a backtracking generator here. *)
  let rec simple_rec env free bound n : Term.t BGen.t =
    let open BGen in
    let open Term in
    if n <= 0
    then
      (* Generate a leaf term. *)
      frequency
        [ (3, mkVar <$> oneofl bound)
        ; (3, mkVar <$> oneofl free)
        ; (5, mkCst <$> (fst <$> oneofl (Name.Map.bindings env.Env.constants)))
        ; (1, lift gen_sort)
        ]
    else
      (* Generate a term with children. *)
      let* n1, n2 = lift @@ split_nat (n - 1) in
      let gen_lambda =
        let* x = lift gen_name in
        mkLambda x
        <$> simple_rec env free bound n1
        <*> simple_rec env free (x :: bound) n2
      in
      let gen_prod =
        let* x = lift gen_name in
        mkProd x
        <$> simple_rec env free bound n1
        <*> simple_rec env free (x :: bound) n2
      in
      let gen_arrow =
        mkArrow
        <$> simple_rec env free bound n1
        <*> simple_rec env free bound n2
      in
      let gen_app =
        mkApp <$> simple_rec env free bound n1 <*> simple_rec env free bound n2
      in
      frequency [ (1, gen_lambda); (1, gen_prod); (1, gen_arrow); (4, gen_app) ]

  let simple ~closed env : Term.t Gen.t =
    let open Gen in
    (* This is quite fast, we can afford to generate large terms. *)
    let* n = 0 -- 100 in
    (* Generate the set of free variables we will choose from. *)
    let* free = if closed then return [] else list gen_name in
    (* Run the algorithm. *)
    BGen.run @@ simple_rec env free [] n

  (*************************************************************************************)
  (** Well-typed term generation. *)

  (** [vars_by_type ty bound free] returns the names of all variables which have type [ty].
      It takes shadowing into account. *)
  let vars_by_type (ty : Term.t) ~bound ~free =
    let rec loop prev acc = function
      | [] -> List.rev acc
      | (v, vty) :: next ->
          if vty = ty && not (List.mem v prev)
          then loop (v :: prev) (v :: acc) next
          else loop (v :: prev) acc next
    in
    (loop [] [] bound, loop (List.map fst bound) [] free)

  (** We use a backtracking generator. *)
  let rec typed_rec (env : Env.t) (free : (Name.t * Term.t) list)
      (bound : (Name.t * Term.t) list) (n : int) (ty : Term.t) : Term.t BGen.t =
    let open BGen in
    let open Term in
    if n <= 0
    then
      (* Get the list of local variables that have the right type.
         We take care to remove variables that are shadowed. *)
      let bound_vars, free_vars = vars_by_type ty ~free ~bound in
      (* Get the list of constants that have the right type. *)
      let consts =
        List.filter_map
          (fun (c, cty) -> if cty = ty then Some c else None)
          (Name.Map.bindings env.Env.constants)
      in
      frequency
        [ (3, mkVar <$> oneofl free_vars)
        ; (3, mkVar <$> oneofl bound_vars)
        ; (5, mkCst <$> oneofl consts)
        ; (1, cond (ty = Sort `Type) @@ lift gen_sort)
        ]
    else
      (* Generate a term with children. *)
      let* n1, n2 = lift @@ split_nat (n - 1) in
      let gen_lambda =
        (* We can only generate a lambda if [ty] is an arrow or dependent product. *)
        match ty with
        | Arrow (ty1, ty2) ->
            let* x = lift gen_name in
            mkLambda x ty1
            <$> typed_rec env free ((x, ty1) :: bound) (n - 1) ty2
        | Prod (y, ty1, ty2) ->
            let* x = lift gen_name in
            (* Replace [y] by [x] in [ty2]. *)
            let ty2 = TermUtils.subst y (mkVar x) ty2 in
            mkLambda x ty1
            <$> typed_rec env free ((x, ty1) :: bound) (n - 1) ty2
        | _ -> fail ()
      in
      let gen_prod =
        (* We can generate a dependent product it [ty] is a sort (Prop or Type). *)
        match ty with
        | Sort _ ->
            let* x = lift gen_name in
            let* x_ty = typed_rec env free bound n1 =<< lift gen_sort in
            mkProd x x_ty <$> typed_rec env free ((x, x_ty) :: bound) n2 ty
        | _ -> fail ()
      in
      let gen_arrow =
        (* We can generate an arrow if [ty] is a sort (Prop or Type). *)
        match ty with
        | Sort _ ->
            mkArrow
            <$> (typed_rec env free bound n1 =<< lift gen_sort)
            <*> typed_rec env free bound n2 ty
        | _ -> fail ()
      in
      let gen_app = fail () in
      frequency [ (1, gen_lambda); (1, gen_prod); (1, gen_arrow); (4, gen_app) ]

  let context env =
    let open Gen in
    small_list
      begin
        let* name = gen_name in
        (* For the type we need something that is :
           - not too slow to compute.
           - simple and realistic so that it is likely to occur in generated programs.
           I went for the heuristic of using the type of a constant that is in the environment. *)
        let* ty =
          frequency
            [ (3, snd <$> oneofl @@ Name.Map.bindings env.Env.constants)
            ; (1, gen_sort)
            ]
        in
        return (name, ty)
      end

  let typed ?(context = []) env ty : Term.t Gen.t =
    let open Gen in
    (* Generating big terms can be slow, we can't increase the size too much. *)
    let* n = 0 -- 50 in
    (* Generate the term. *)
    BGen.run @@ typed_rec env context [] n ty
end
