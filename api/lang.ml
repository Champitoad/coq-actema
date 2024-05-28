open Utils.Pervasive

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

  let eq = make "Coq.Init.Logic.eq"
  let nat = make "Coq.Init.Datatypes.nat"
  let list = make "Coq.Init.Datatypes.list"
  let and_ = make "Coq.Init.Logic.and"
  let or_ = make "Coq.Init.Logic.or"
  let not = make "Coq.Init.Logic.not"
  let equiv = make "Coq.Init.Logic.iff"
  let ex = make "Coq.Init.Logic.ex"
  let zero = make "Coq.Init.Datatypes.O"
  let succ = make "Coq.Init.Datatypes.S"
  let eq = make "Coq.Init.Logic.eq"
  let true_ = make "Coq.Init.Logic.True"
  let false_ = make "Coq.Init.Logic.False"
  let add = make "Coq.Init.Nat.add"
  let mul = make "Coq.Init.Nat.mul"

  let is_logical_conn name : bool =
    List.exists (equal name) [ and_; or_; not; equiv; true_; false_ ]
end

(***************************************************************************************)
(** Terms *)

module Term = struct
  type t =
    | Var of int
    | App of t * t list
    | Lambda of Name.t * t * t
    | Arrow of t * t
    | Prod of Name.t * t * t
    | Cst of Name.t
    | Sort of [ `Prop | `Type ]
  [@@deriving show]

  let mkVar n =
    assert (n >= 0);
    Var n

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

exception InvalidSubtermPath of Term.t * int list

(***************************************************************************************)
(** Typing contexts. *)

module Context = struct
  type t = (Name.t * Term.t) list [@@deriving show]

  let empty = []
  let size ctx = List.length ctx
  let push name ty ctx = (name, ty) :: ctx
  let pop ctx = match ctx with [] -> None | _ :: ctx -> Some ctx
  let get i ctx = List.nth_opt ctx i

  let get_by_type ty ctx =
    ctx
    |> List.mapi (fun i (_, ty') -> if ty = ty' then Some i else None)
    |> List.filter_map Fun.id

  let stack ctx1 ctx2 = ctx1 @ ctx2
  let to_list ctx = ctx
  let of_list ctx = ctx
end

(***************************************************************************************)
(** Environments *)

module Env = struct
  type pp_pos = Prefix | Infix | Suffix [@@deriving show]

  type pp_info =
    { symbol : string; implicit_args : int list; position : pp_pos }
  [@@deriving show]

  type t = { constants : Term.t Name.Map.t; pp_info : pp_info Name.Map.t }

  let empty = { constants = Name.Map.empty; pp_info = Name.Map.empty }

  let union env1 env2 =
    let check_binding name v1 v2 = if v1 = v2 then Some v1 else assert false in
    { constants = Name.Map.union check_binding env1.constants env2.constants
    ; pp_info = Name.Map.union check_binding env1.pp_info env2.pp_info
    }

  let add_constant name ty ?pp env =
    let env = { env with constants = Name.Map.add name ty env.constants } in
    match pp with
    | None -> env
    | Some pp -> { env with pp_info = Name.Map.add name pp env.pp_info }

  let default_pp_info symbol = { symbol; implicit_args = []; position = Prefix }

  let filter_args pp_info args =
    let rec loop implicits args kept i =
      match (args, implicits) with
      | arg :: args, imp :: implicits ->
          if i = imp
          then loop implicits args kept (i + 1)
          else loop (imp :: implicits) args (arg :: kept) (i + 1)
      | _, [] ->
          (* All the remaining arguments are explicit. *) List.rev kept @ args
      | [], _ :: _ ->
          (* There are remaining implicits but no more args. *) assert false
    in
    loop (List.sort Int.compare pp_info.implicit_args) args [] 0

  let test_env =
    let open Term in
    let nat = mkCst @@ Name.nat in
    let constants =
      [ (Name.true_, mkProp)
      ; (Name.false_, mkProp)
      ; (Name.or_, mkArrows [ mkProp; mkProp; mkProp ])
      ; (Name.and_, mkArrows [ mkProp; mkProp; mkProp ])
      ; (Name.not, mkArrow mkProp mkProp)
      ; (Name.equiv, mkArrows [ mkProp; mkProp; mkProp ])
      ; (Name.nat, mkType)
      ; (Name.zero, nat)
      ; (Name.succ, mkArrow nat nat)
      ; (Name.add, mkArrows [ nat; nat; nat ])
      ; (Name.mul, mkArrows [ nat; nat; nat ])
      ; ( Name.eq
        , mkProd (Name.make "A") mkType @@ mkArrows [ mkVar 0; mkVar 0; mkProp ]
        )
      ; ( Name.ex
        , mkProd (Name.make "A") mkType
          @@ mkArrow (mkArrow (mkVar 0) mkProp) mkProp )
      ]
    in
    List.fold_left
      (fun env (name, ty) -> add_constant name ty env)
      empty constants
end

(***************************************************************************************)
(** Term utility functions. *)

module TermUtils = struct
  let rec alpha_equiv (t1 : Term.t) (t2 : Term.t) : bool =
    match (t1, t2) with
    | Var v1, Var v2 when v1 = v2 -> true
    | Cst c1, Cst c2 when Name.equal c1 c2 -> true
    | Sort s1, Sort s2 when s1 = s2 -> true
    | Lambda (_, ty1, body1), Lambda (_, ty2, body2) ->
        alpha_equiv ty1 ty2 && alpha_equiv body1 body2
    | Prod (_, ty1, body1), Prod (_, ty2, body2) ->
        alpha_equiv ty1 ty2 && alpha_equiv body1 body2
    | Arrow (a1, b1), Arrow (a2, b2) -> alpha_equiv a1 a2 && alpha_equiv b1 b2
    | App (f1, args1), App (f2, args2)
      when List.length args1 = List.length args2 ->
        List.fold_left ( && ) (alpha_equiv f1 f2)
          (List.map2 alpha_equiv args1 args2)
    | _ -> false

  let rec lift k n t =
    match (t : Term.t) with
    | Var i when i >= k -> Term.mkVar (i + n)
    | Var _ | Cst _ | Sort _ -> t
    | Lambda (x, ty, body) ->
        Term.mkLambda x (lift k n ty) (lift (k + 1) n body)
    | Prod (x, ty, body) -> Term.mkProd x (lift k n ty) (lift (k + 1) n body)
    | Arrow (t1, t2) -> Term.mkArrow (lift k n t1) (lift k n t2)
    | App (f, args) -> Term.mkApps (lift k n f) (List.map (lift k n) args)

  let lift_free n t = lift 0 n t

  let subst k u t =
    let rec loop depth k u t =
      match (t : Term.t) with
      | Var i when i = k -> lift_free depth u
      | Var i when i >= k -> Term.mkVar (i - 1)
      | Var _ | Cst _ | Sort _ -> t
      | Lambda (x, ty, body) ->
          Term.mkLambda x (loop depth k u ty) (loop (depth + 1) (k + 1) u body)
      | Prod (x, ty, body) ->
          Term.mkProd x (loop depth k u ty) (loop (depth + 1) (k + 1) u body)
      | Arrow (t1, t2) -> Term.mkArrow (loop depth k u t1) (loop depth k u t2)
      | App (f, args) ->
          Term.mkApps (loop depth k u f) (List.map (loop depth k u) args)
    in
    loop 0 k u t

  (** [acc] is the list of free variables already found. 
      [depth] is the current depth (number of binders traversed). *)
  let rec free_vars_rec (acc : int list) (depth : int) (t : Term.t) : int list =
    match (t : Term.t) with
    | Var n -> if n >= depth then (n - depth) :: acc else acc
    | Cst _ | Sort _ -> acc
    | App (f, args) ->
        List.fold_left (fun acc t -> free_vars_rec acc depth t) acc (f :: args)
    | Arrow (t1, t2) ->
        let acc = free_vars_rec acc depth t1 in
        let acc = free_vars_rec acc depth t2 in
        acc
    | Lambda (x, ty, body) | Prod (x, ty, body) ->
        let acc = free_vars_rec acc depth ty in
        let acc = free_vars_rec acc (depth + 1) body in
        acc

  let free_vars t = IntSet.of_list @@ free_vars_rec [] 0 t

  let rec constants_rec acc t =
    match (t : Term.t) with
    | Cst c -> c :: acc
    | Var _ | Sort _ -> acc
    | App (f, args) -> List.fold_left constants_rec acc (f :: args)
    | Arrow (t1, t2) ->
        let acc = constants_rec acc t1 in
        let acc = constants_rec acc t2 in
        acc
    | Lambda (x, ty, body) | Prod (x, ty, body) ->
        let acc = constants_rec acc ty in
        let acc = constants_rec acc body in
        acc

  let constants t = Name.Set.of_list @@ constants_rec [] t

  let rec subterm_rec exn ctx t sub : Context.t * Term.t =
    match sub with
    | [] -> (ctx, t)
    | idx :: sub -> begin
        match (t : Term.t) with
        | Var _ | Cst _ | Sort _ -> raise exn
        | App (f, args) ->
            if idx = 0
            then subterm_rec exn ctx f sub
            else if 1 <= idx && idx <= List.length args
            then subterm_rec exn ctx (List.nth args (idx - 1)) sub
            else raise exn
        | Lambda (x, ty, body) | Prod (x, ty, body) ->
            if idx = 0
            then subterm_rec exn ctx ty sub
            else if idx = 1
            then subterm_rec exn (Context.push x ty ctx) body sub
            else raise exn
        | Arrow (t1, t2) ->
            if idx = 0
            then subterm_rec exn ctx t1 sub
            else if idx = 1
            then subterm_rec exn ctx t2 sub
            else raise exn
      end

  let subterm ?(context = Context.empty) t sub =
    let exn = InvalidSubtermPath (t, sub) in
    subterm_rec exn context t sub

  let rec trim_rec (t : Term.t) : Term.t =
    match t with
    | Var _ | Cst _ | Sort _ -> t
    | Lambda (x, ty, body) -> Term.mkLambda x (trim_rec ty) (trim_rec body)
    | Arrow (t1, t2) -> Term.mkArrow (trim_rec t1) (trim_rec t2)
    | App (f, args) -> Term.mkApps (trim_rec f) (List.map trim_rec args)
    | Prod (x, ty, body) ->
        let ty = trim_rec ty in
        let body = trim_rec body in
        if IntSet.mem 0 (free_vars body)
        then Term.mkProd x ty body
        else Term.mkArrow ty (lift_free (-1) body)

  let trim_products t = trim_rec t
end

(***************************************************************************************)
(** Typing. *)

module Typing = struct
  (** See the error messages in [pp_typeError] for an explanation of 
      the different error cases. *)
  type typeError =
    | UnboundVar of int
    | UnboundCst of Name.t
    | ExpectedType of Term.t * Term.t * Term.t
    | ExpectedFunction of Term.t * Term.t
    | ExpectedSort of Term.t * Term.t

  let pp_typeError fmt err =
    match err with
    | UnboundVar n -> Format.fprintf fmt "Unbound variable: %d" n
    | UnboundCst c -> Format.fprintf fmt "Unbound constant: %s" (Name.show c)
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
  let rec check_rec env (ctx : Context.t) t : Term.t =
    match (t : Term.t) with
    | Var n -> begin
        match Context.get n ctx with
        | None -> raise @@ TypingError (UnboundVar n)
        | Some (_, ty) -> ty
      end
    | Cst c -> begin
        match Name.Map.find_opt c env.Env.constants with
        | None -> raise @@ TypingError (UnboundCst c)
        | Some ty -> ty
      end
    | Sort _ -> Sort `Type
    | Lambda (x, ty, body) ->
        let _ = check_rec env ctx ty in
        let body_ty = check_rec env (Context.push x ty ctx) body in
        (* Depending on whether [x] appears in [body_ty],
           this is a dependent or non-dependent product. *)
        if IntSet.mem 0 (TermUtils.free_vars body_ty)
        then Term.mkProd x ty body_ty
        else
          (* We remove a binder so we lower the body type by 1. *)
          Term.mkArrow ty (TermUtils.lift_free (-1) body_ty)
    | App (f, args) ->
        let _res, res_ty =
          List.fold_left (check_app env ctx) (f, check_rec env ctx f) args
        in
        res_ty
    | Arrow (a, b) -> begin
        let a_ty = check_rec env ctx a in
        let b_ty = check_rec env ctx b in
        match (a_ty, b_ty) with
        | Sort _, Sort _ -> b_ty
        | Sort _, _ -> raise @@ TypingError (ExpectedSort (b, b_ty))
        | _, _ -> raise @@ TypingError (ExpectedSort (a, a_ty))
      end
    | Prod (x, a, b) -> begin
        let a_ty = check_rec env ctx a in
        let b_ty = check_rec env (Context.push x a ctx) b in
        match (a_ty, b_ty) with
        | Sort _, Sort _ -> b_ty
        | Sort _, _ -> raise @@ TypingError (ExpectedSort (b, b_ty))
        | _, _ -> raise @@ TypingError (ExpectedSort (a, a_ty))
      end

  (** Type-check an application with a single argument. 
      It takes as argument (and returns) a pair [term, type_]. *)
  and check_app env ctx (f, f_ty) arg =
    let arg_ty = check_rec env ctx arg in
    match f_ty with
    | Arrow (a, b) ->
        if arg_ty = a
        then (Term.mkApp f arg, b)
        else raise @@ TypingError (ExpectedType (arg, arg_ty, a))
    | Prod (x, a, b) ->
        if arg_ty = a
        then (Term.mkApp f arg, TermUtils.subst 0 arg b)
        else raise @@ TypingError (ExpectedType (arg, arg_ty, a))
    | _ -> raise @@ TypingError (ExpectedFunction (f, f_ty))

  let check ?(context = Context.empty) env t = check_rec env context t

  (** TODO: actually makes this faster. *)
  let typeof ?(context = Context.empty) env t = check ~context env t
end

(***************************************************************************************)
(** Random term generation. *)

module TermGen = struct
  open QCheck2
  open Utils

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

  let range ofs len = List.init len (fun i -> i + ofs)

  (*************************************************************************************)
  (** Simple term generation. *)

  (** We use a backtracking generator here. 
      The context [ctx_free] is for variables that are free in the resulting term,
      and [ctx_bound] is for variables that are bound in the resulting term.
      The typing information in [ctx_bound] and [ctx_free] is irrelevant : we use only the names. *)
  let rec simple_rec env ctx_bound ctx_free n : Term.t BGen.t =
    let open BGen in
    let open Term in
    if n <= 0
    then
      (* Generate a leaf term. *)
      let bound_size = Context.size ctx_bound in
      let bound = range 0 bound_size in
      let free = range bound_size (Context.size ctx_free) in
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
        <$> simple_rec env ctx_bound ctx_free n1
        <*> simple_rec env (Context.push x Term.mkType ctx_bound) ctx_free n2
      in
      let gen_prod =
        let* x = lift gen_name in
        mkProd x
        <$> simple_rec env ctx_bound ctx_free n1
        <*> simple_rec env (Context.push x Term.mkType ctx_bound) ctx_free n2
      in
      let gen_arrow =
        mkArrow
        <$> simple_rec env ctx_bound ctx_free n1
        <*> simple_rec env ctx_bound ctx_free n2
      in
      let gen_app =
        mkApp
        <$> simple_rec env ctx_bound ctx_free n1
        <*> simple_rec env ctx_bound ctx_free n2
      in
      frequency [ (1, gen_lambda); (1, gen_prod); (1, gen_arrow); (4, gen_app) ]

  let simple ~closed env : Term.t Gen.t =
    let open Gen in
    (* This is quite fast, we can afford to generate large terms. *)
    let* n = 0 -- 100 in
    (* Generate the set of free variables we will choose from. *)
    let* ctx =
      if closed
      then return Context.empty
      else
        let+ names = small_list gen_name in
        List.fold_left
          (fun ctx n -> Context.push n Term.mkType ctx)
          Context.empty names
    in
    (* Run the algorithm. *)
    BGen.run @@ simple_rec env Context.empty ctx n

  (*************************************************************************************)
  (** Well-typed term generation. *)

  (** We use a backtracking generator. *)
  let rec typed_rec (env : Env.t) ctx_bound ctx_free (n : int) (ty : Term.t) :
      Term.t BGen.t =
    let open BGen in
    let open Term in
    if n <= 0
    then
      (* Get the list of local variables that have the right type. *)
      let bound = Context.get_by_type ty ctx_bound in
      let free =
        Context.get_by_type ty ctx_free
        |> List.map (Int.add @@ Context.size ctx_bound)
      in
      (* Get the list of constants that have the right type. *)
      let consts =
        List.filter_map
          (fun (c, cty) -> if cty = ty then Some c else None)
          (Name.Map.bindings env.Env.constants)
      in
      frequency
        [ (3, mkVar <$> oneofl free)
        ; (3, mkVar <$> oneofl bound)
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
            <$> typed_rec env
                  (Context.push x ty1 ctx_bound)
                  ctx_free (n - 1) ty2
        | Prod (y, ty1, ty2) ->
            let* x = lift gen_name in
            mkLambda x ty1
            <$> typed_rec env
                  (Context.push x ty1 ctx_bound)
                  ctx_free (n - 1) ty2
        | _ -> fail ()
      in
      let gen_prod =
        (* We can generate a dependent product it [ty] is a sort (Prop or Type). *)
        match ty with
        | Sort _ ->
            let* x = lift gen_name in
            let* x_ty = typed_rec env ctx_bound ctx_free n1 =<< lift gen_sort in
            mkProd x x_ty
            <$> typed_rec env (Context.push x x_ty ctx_bound) ctx_free n2 ty
        | _ -> fail ()
      in
      let gen_arrow =
        (* We can generate an arrow if [ty] is a sort (Prop or Type). *)
        match ty with
        | Sort _ ->
            mkArrow
            <$> (typed_rec env ctx_bound ctx_free n1 =<< lift gen_sort)
            <*> typed_rec env ctx_bound ctx_free n2 ty
        | _ -> fail ()
      in
      let gen_app = fail () in
      frequency [ (1, gen_lambda); (1, gen_prod); (1, gen_arrow); (4, gen_app) ]

  (** Generate a simple type in [env]. *)
  let simple_type env =
    let open Gen in
    (* For the type we need something that is :
       - not too slow to compute.
       - simple and realistic so that it is likely to occur in generated programs.
       I went for the heuristic of using the type of a constant that is in the environment. *)
    frequency
      [ (3, snd <$> oneofl @@ Name.Map.bindings env.Env.constants)
      ; (1, gen_sort)
      ]

  let context env =
    let open Gen in
    let+ bindings = small_list @@ pair gen_name (simple_type env) in
    Context.of_list bindings

  let typed ?(context = []) ?ty env =
    let open Gen in
    match ty with
    | None ->
        (* Choose a size.*)
        let* n = 0 -- 5 in
        (* Choose a target type. We have to be careful to choose an inhabited type. *)
        let* ty = match ty with Some ty -> return ty | None -> gen_sort in
        (* Generate a term. *)
        let* term = BGen.run @@ typed_rec env context [] n ty in
        return (term, ty)
    | Some ty ->
        BGen.run
          begin
            let open Utils.BGen in
            let* n = lift Gen.(0 -- 10) in
            let+ term = typed_rec env context [] n ty in
            (term, ty)
          end
end
