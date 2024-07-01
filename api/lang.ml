open Utils.Pervasive

(***************************************************************************************)
(** Free variables. *)

module FVarId : sig
  type t [@@deriving show]

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int

  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t
  module Hashtbl : Hashtbl.S with type key = t

  (** This exposes the implementation of free variables, and is only available in this file
      (you can check it is not exposed in lang.mli). 
      It is used in [Context.fresh_fvar]. *)
  val unsafe_from_int : int -> t

  (** This exposes the implementation of free variables, and is only available in this file
      (you can check it is not exposed in lang.mli). 
      It is used in [Context.fresh_fvar]. *)
  val unsafe_to_int : t -> int
end = struct
  type t = int [@@deriving show]

  let equal = Int.equal
  let compare = Int.compare
  let hash = Hashtbl.hash

  module Set = IntSet
  module Map = IntMap

  module Hashtbl = Hashtbl.Make (struct
    type t = int

    let hash = Hashtbl.hash
    let equal = Int.equal
  end)

  let unsafe_from_int fvar = fvar
  let unsafe_to_int fvar = fvar
end

(***************************************************************************************)
(** Terms *)

module Term = struct
  (** Some cached data attached to a term. 
      If we were really serious about performance we would stack all the fields into a single integer,
      but here we prefer ease of use. *)
  type cdata =
    { (* Does this term contain free variables (FVars) ? *)
      contains_fvars : bool
    ; (* This term contains loose BVars in range [0..loose_bvar_range-1].
         In particular when loose_vars is 0, the term contains no loose bvars. *)
      loose_bvar_range : int
    }

  type binder = Anonymous | Named of Name.t [@@deriving show]

  type t =
    | BVar of int
    | FVar of FVarId.t
    | Cst of Name.t
    | Sort of [ `Prop | `Type ]
    | App of (cdata[@opaque]) * t * t list
    | Lambda of (cdata[@opaque]) * binder * t * t
    | Prod of (cdata[@opaque]) * binder * t * t
  [@@deriving show]

  (** Compute or retrieve the cached data associated to a term. This is O(1). *)
  let get_cdata term : cdata =
    match term with
    | BVar n -> { contains_fvars = false; loose_bvar_range = n + 1 }
    | FVar name -> { contains_fvars = true; loose_bvar_range = 0 }
    | Cst _ -> { contains_fvars = false; loose_bvar_range = 0 }
    | Sort _ -> { contains_fvars = false; loose_bvar_range = 0 }
    | App (cdata, _, _) | Lambda (cdata, _, _, _) | Prod (cdata, _, _, _) ->
        cdata

  (** Merge two [cdata]s.  *)
  let merge_cdata c1 c2 : cdata =
    { contains_fvars = c1.contains_fvars || c2.contains_fvars
    ; loose_bvar_range = max c1.loose_bvar_range c2.loose_bvar_range
    }

  (** Lift a [cdata] through a binder. 
      This is what is used e.g. when calculating the cdata of a [Lambda].*)
  let lift_cdata c : cdata =
    { contains_fvars = c.contains_fvars
    ; loose_bvar_range =
        (if c.loose_bvar_range > 0 then c.loose_bvar_range - 1 else 0)
    }

  let mkBVar n =
    assert (n >= 0);
    BVar n

  let mkFVar name = FVar name
  let mkCst name = Cst name
  let mkProp = Sort `Prop
  let mkType = Sort `Type
  let mkSort s = Sort s

  let mkApp f arg =
    match f with
    | App (cdata, f, f_args) ->
        let cdata = merge_cdata cdata (get_cdata arg) in
        App (cdata, f, f_args @ [ arg ])
    | _ ->
        let cdata = merge_cdata (get_cdata f) (get_cdata arg) in
        App (cdata, f, [ arg ])

  let mkApps f args =
    if args = []
    then f
    else
      match f with
      | App (cdata, f, f_args) ->
          let cdata =
            List.fold_left merge_cdata cdata (List.map get_cdata args)
          in
          App (cdata, f, f_args @ args)
      | _ ->
          let cdata =
            List.fold_left merge_cdata (get_cdata f) (List.map get_cdata args)
          in
          App (cdata, f, args)

  let mkLambda binder ty body =
    let cdata = merge_cdata (get_cdata ty) (lift_cdata @@ get_cdata body) in
    Lambda (cdata, binder, ty, body)

  let mkProd binder ty body =
    let cdata = merge_cdata (get_cdata ty) (lift_cdata @@ get_cdata body) in
    Prod (cdata, binder, ty, body)

  let contains_fvars term = (get_cdata term).contains_fvars
  let loose_bvar_range term = (get_cdata term).loose_bvar_range
  let contains_loose_bvars term = (get_cdata term).loose_bvar_range > 0

  (** [lift_rec depth n term] adds [n] to every loose bvar of [term] that is greater or equal to [depth].
      This takes advantage of [cdata] to speed things up. *)
  let rec lift_rec depth n term =
    match term with
    | BVar idx when idx >= depth -> mkBVar (idx + n)
    | FVar _ | Cst _ | Sort _ | BVar _ -> term
    | App (cdata, f, args) ->
        if cdata.loose_bvar_range <= depth
        then term
        else mkApps (lift_rec depth n f) @@ List.map (lift_rec depth n) args
    | Lambda (cdata, x, ty, body) ->
        if cdata.loose_bvar_range <= depth
        then term
        else mkLambda x (lift_rec depth n ty) (lift_rec (depth + 1) n body)
    | Prod (cdata, x, ty, body) ->
        if cdata.loose_bvar_range <= depth
        then term
        else mkProd x (lift_rec depth n ty) (lift_rec (depth + 1) n body)

  let lift n term = lift_rec 0 n term

  let mkArrow t1 t2 =
    let cdata = merge_cdata (get_cdata t1) (lift_cdata @@ get_cdata t2) in
    Prod (cdata, Anonymous, t1, lift 1 t2)

  let mkArrows ts =
    match List.rev ts with
    | [] -> failwith "Term.mkArrows : got an empty list."
    | t :: ts -> List.fold_right mkArrow (List.rev ts) t

  (** [fsubst_rec depth subst term] replaces each [FVar fvar] 
      by [lift depth @@ subst fvar] in [term]. 
      This takes advantage of [cdata] to speed things up. *)
  let rec fsubst_rec depth subst term =
    match term with
    | FVar fvar -> lift depth @@ subst fvar
    | BVar _ | Cst _ | Sort _ -> term
    | App (cdata, f, args) ->
        if not cdata.contains_fvars
        then term
        else
          mkApps (fsubst_rec depth subst f)
          @@ List.map (fsubst_rec depth subst) args
    | Lambda (cdata, x, ty, body) ->
        if not cdata.contains_fvars
        then term
        else
          mkLambda x
            (fsubst_rec depth subst ty)
            (fsubst_rec (depth + 1) subst body)
    | Prod (cdata, x, ty, body) ->
        if not cdata.contains_fvars
        then term
        else
          mkProd x
            (fsubst_rec depth subst ty)
            (fsubst_rec (depth + 1) subst body)

  let fsubst subst term = fsubst_rec 0 subst term

  let abstract fvar term =
    let subst fvar' =
      if FVarId.equal fvar fvar' then mkBVar 0 else mkFVar fvar'
    in
    fsubst subst term

  (** [bsubst_rec depth subst term] replaces bvar [BVar n] for [n >= depth] 
      by [lift depth @@ subst (n - depth)] in [term].
      This takes advantage of [cdata] to speed things up. *)
  let rec bsubst_rec depth subst term =
    match term with
    | BVar n when n >= depth -> lift depth @@ subst (n - depth)
    | Cst _ | FVar _ | Sort _ | BVar _ -> term
    | App (cdata, f, args) ->
        if cdata.loose_bvar_range <= depth
        then term
        else
          mkApps (bsubst_rec depth subst f)
          @@ List.map (bsubst_rec depth subst) args
    | Lambda (cdata, x, ty, body) ->
        if cdata.loose_bvar_range <= depth
        then term
        else
          mkLambda x
            (bsubst_rec depth subst ty)
            (bsubst_rec (depth + 1) subst body)
    | Prod (cdata, x, ty, body) ->
        if cdata.loose_bvar_range <= depth
        then term
        else
          mkProd x
            (bsubst_rec depth subst ty)
            (bsubst_rec (depth + 1) subst body)

  let bsubst subst term = bsubst_rec 0 subst term
  let bsubst0 s term = bsubst (function 0 -> s | n -> mkBVar (n - 1)) term
  let instantiate fvar term = bsubst0 (mkFVar fvar) term

  let rec alpha_equiv t1 t2 : bool =
    match (t1, t2) with
    | BVar b1, BVar b2 when b1 = b2 -> true
    | FVar f1, FVar f2 when FVarId.equal f1 f2 -> true
    | Cst c1, Cst c2 when Name.equal c1 c2 -> true
    | Sort s1, Sort s2 when s1 = s2 -> true
    | Lambda (_, _, ty1, body1), Lambda (_, _, ty2, body2) ->
        alpha_equiv ty1 ty2 && alpha_equiv body1 body2
    | Prod (_, _, ty1, body1), Prod (_, _, ty2, body2) ->
        alpha_equiv ty1 ty2 && alpha_equiv body1 body2
    | App (_, f1, args1), App (_, f2, args2)
      when List.length args1 = List.length args2 ->
        List.for_all2 alpha_equiv (f1 :: args1) (f2 :: args2)
    | _ -> false

  let rec fvars_rec acc term : FVarId.t list =
    match term with
    | FVar fvar -> fvar :: acc
    | BVar _ | Sort _ | Cst _ -> acc
    | App (cdata, f, args) ->
        if not cdata.contains_fvars
        then acc
        else List.fold_left fvars_rec acc (f :: args)
    | Lambda (cdata, _, ty, body) | Prod (cdata, _, ty, body) ->
        if not cdata.contains_fvars
        then acc
        else
          let acc = fvars_rec acc ty in
          fvars_rec acc body

  let free_vars term = fvars_rec [] term

  let rec bvars_rec depth acc term : int list =
    match term with
    | BVar n when depth <= n -> (n - depth) :: acc
    | FVar _ | Sort _ | Cst _ | BVar _ -> acc
    | App (cdata, f, args) ->
        if cdata.loose_bvar_range <= depth
        then acc
        else List.fold_left (bvars_rec depth) acc (f :: args)
    | Lambda (cdata, _, ty, body) | Prod (cdata, _, ty, body) ->
        if cdata.loose_bvar_range <= depth
        then acc
        else
          let acc = bvars_rec depth acc ty in
          bvars_rec (depth + 1) acc body

  let loose_bvars term = bvars_rec 0 [] term

  let rec csts_rec acc term =
    match term with
    | Cst name -> name :: acc
    | BVar _ | FVar _ | Sort _ -> acc
    | App (cdata, f, args) ->
        if not cdata.contains_fvars
        then acc
        else List.fold_left csts_rec acc (f :: args)
    | Lambda (cdata, _, ty, body) | Prod (cdata, _, ty, body) ->
        if not cdata.contains_fvars
        then acc
        else
          let acc = csts_rec acc ty in
          csts_rec acc body

  let constants term = csts_rec [] term
end

exception InvalidSubtermPath of Term.t * int list

(***************************************************************************************)
(** Local context, which holds information about free variables. *)

module Context = struct
  type entry = { binder : Term.binder; type_ : Term.t } [@@deriving show]

  let pp_context fmt ctx =
    let bindings = FVarId.Map.bindings ctx in
    Format.fprintf fmt "%s" ([%derive.show: (FVarId.t * entry) list] bindings)

  type t =
    { (* A map from free variable identiers to entries. *)
      map : entry FVarId.Map.t [@printer pp_context]
    }
  [@@deriving show]

  (** The empty typing context. *)
  let empty = { map = FVarId.Map.empty }

  let size ctx = FVarId.Map.cardinal ctx.map

  let add fvar binder type_ ctx =
    let entry = { binder; type_ } in
    { map = FVarId.Map.add fvar entry ctx.map }

  let add_fresh binder type_ ctx =
    let fvar =
      (* A context is in charge of generating a free variable,
         so it needs access to the internal representation of FVarId. *)
      match FVarId.Map.max_binding_opt ctx.map with
      | None -> FVarId.unsafe_from_int 0
      | Some (fvar, _) -> FVarId.unsafe_from_int (1 + FVarId.unsafe_to_int fvar)
    in
    (fvar, add fvar binder type_ ctx)

  let mem fvar ctx = FVarId.Map.mem fvar ctx.map
  let find fvar ctx = FVarId.Map.find_opt fvar ctx.map
  let remove fvar ctx = { map = FVarId.Map.remove fvar ctx.map }
  let domain ctx = List.of_enum @@ FVarId.Map.keys ctx.map
end

(***************************************************************************************)
(** Predefined constants *)

module Constants = struct
  open Name

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
  let nil = make "Coq.Init.Datatypes.nil"
  let cons = make "Coq.Init.Datatypes.cons"

  let is_logical_conn name : bool =
    List.exists (equal name) [ and_; or_; not; equiv; true_; false_ ]
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
    let nat = mkCst @@ Constants.nat in
    let constants =
      [ (Constants.true_, mkProp)
      ; (Constants.false_, mkProp)
      ; (Constants.or_, mkArrows [ mkProp; mkProp; mkProp ])
      ; (Constants.and_, mkArrows [ mkProp; mkProp; mkProp ])
      ; (Constants.not, mkArrow mkProp mkProp)
      ; (Constants.equiv, mkArrows [ mkProp; mkProp; mkProp ])
      ; (Constants.nat, mkType)
      ; (Constants.zero, nat)
      ; (Constants.succ, mkArrow nat nat)
      ; (Constants.add, mkArrows [ nat; nat; nat ])
      ; (Constants.mul, mkArrows [ nat; nat; nat ])
      ; ( Constants.eq
        , mkProd (Named (Name.make "A")) mkType
          @@ mkArrows [ mkBVar 0; mkBVar 0; mkProp ] )
      ; ( Constants.ex
        , mkProd (Named (Name.make "A")) mkType
          @@ mkArrow (mkArrow (mkBVar 0) mkProp) mkProp )
      ]
    in
    List.fold_left
      (fun env (name, ty) -> add_constant name ty env)
      empty constants
end

(***************************************************************************************)

(** Manipulating terms. *)
module TermUtils = struct
  let rec subterm_rec ctx t sub : Context.t * Term.t =
    match sub with
    | [] -> (ctx, t)
    | idx :: sub -> begin
        match (t : Term.t) with
        | App (_, f, args) when idx = 0 -> subterm_rec ctx f sub
        | App (_, f, args) when 1 <= idx && idx <= List.length args ->
            subterm_rec ctx (List.nth args (idx - 1)) sub
        | (Lambda (_, x, ty, body) | Prod (_, x, ty, body)) when idx = 0 ->
            subterm_rec ctx ty sub
        | (Lambda (_, x, ty, body) | Prod (_, x, ty, body)) when idx = 1 ->
            (* Add x to the context. *)
            let fvar, new_ctx = Context.add_fresh x ty ctx in
            (* Recurse with the new context. *)
            subterm_rec new_ctx (Term.instantiate fvar body) sub
        | _ -> failwith "subterm_rec : invalid path"
      end

  let subterm ?(context = Context.empty) t sub =
    try subterm_rec context t sub
    with Failure _ -> raise @@ InvalidSubtermPath (t, sub)

  (** See the error messages in [pp_typeError] for an explanation of
        the different error cases. *)
  type typeError =
    | LooseBVar of int
    | UnboundFVar of FVarId.t
    | UnboundCst of Name.t
    | ExpectedType of Term.t * Term.t * Term.t
    | ExpectedFunction of Term.t * Term.t
    | ExpectedSort of Term.t * Term.t

  let pp_typeError fmt err =
    match err with
    | LooseBVar n -> Format.fprintf fmt "Loose bound variable : %d" n
    | UnboundFVar fvar ->
        Format.fprintf fmt "Unbound free variable: %s" (FVarId.show fvar)
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

  let rec check_rec env ctx t : Term.t =
    match (t : Term.t) with
    | BVar n -> raise @@ TypingError (LooseBVar n)
    | FVar fvar -> begin
        match Context.find fvar ctx with
        | None -> raise @@ TypingError (UnboundFVar fvar)
        | Some entry -> entry.type_
      end
    | Cst c -> begin
        match Name.Map.find_opt c env.Env.constants with
        | None -> raise @@ TypingError (UnboundCst c)
        | Some ty -> ty
      end
    | Sort _ -> Sort `Type
    | Lambda (_, x, ty, body) ->
        (* Check the type. *)
        let _ = check_sort env ctx ty in
        (* Check the body. *)
        let fvar, new_ctx = Context.add_fresh x ty ctx in
        let body_ty = check_rec env new_ctx @@ Term.instantiate fvar body in
        (* Don't forget to abstract the body type. *)
        Term.mkProd x ty @@ Term.abstract fvar body_ty
    | App (_, f, args) ->
        let _, res_ty =
          List.fold_left (check_app env ctx) (f, check_rec env ctx f) args
        in
        res_ty
    | Prod (_, x, ty, body) ->
        (* Type check the type. *)
        let _ = check_sort env ctx ty in
        (* Type check the body. *)
        let fvar, ctx = Context.add_fresh x ty ctx in
        let body_sort = check_sort env ctx @@ Term.instantiate fvar body in
        Term.mkSort body_sort

  (** Type-check an application with a single argument.
            It takes as argument (and returns) a pair [term, type_]. *)
  and check_app env ctx (f, f_ty) arg =
    let arg_ty = check_rec env ctx arg in
    match (f_ty : Term.t) with
    | Prod (_, x, a, b) ->
        if Term.alpha_equiv arg_ty a
        then (Term.mkApp f arg, Term.bsubst0 arg b)
        else raise @@ TypingError (ExpectedType (arg, arg_ty, a))
    | _ -> raise @@ TypingError (ExpectedFunction (f, f_ty))

  and check_sort env ctx term =
    let ty = check_rec env ctx term in
    match ty with
    | Sort s -> s
    | _ -> raise @@ TypingError (ExpectedSort (term, ty))

  let check env context term = check_rec env context term

  let well_typed env context term =
    try
      ignore (check env context term);
      true
    with TypingError _ -> false

  (* Some performance optimizations compared to [check] :
     - We don't re-check the type of the arguments in applications
       and the type of the binder in lambda abstractions and products.
  *)
  let rec typeof_rec env ctx t : Term.t =
    match (t : Term.t) with
    | BVar n -> raise @@ TypingError (LooseBVar n)
    | FVar fvar ->
        let entry = Option.get @@ Context.find fvar ctx in
        entry.type_
    | Cst c -> Option.get @@ Name.Map.find_opt c env.Env.constants
    | Sort _ -> Sort `Type
    | Lambda (_, x, ty, body) ->
        let fvar, new_ctx = Context.add_fresh x ty ctx in
        let body_ty = typeof_rec env new_ctx @@ Term.instantiate fvar body in
        (* Don't forget to abstract the body type. *)
        Term.mkProd x ty @@ Term.abstract fvar body_ty
    | App (_, f, args) ->
        let _, res_ty =
          List.fold_left (typeof_app env ctx) (f, typeof_rec env ctx f) args
        in
        res_ty
    | Prod (_, x, ty, body) ->
        (* Type check the body. *)
        let fvar, ctx = Context.add_fresh x ty ctx in
        typeof_rec env ctx @@ Term.instantiate fvar body

  (** Type-check an application with a single argument.
      It takes as argument (and returns) a pair [term, type_]. *)
  and typeof_app env ctx (f, f_ty) arg =
    match (f_ty : Term.t) with
    | Prod (_, x, a, b) -> (Term.mkApp f arg, Term.bsubst0 arg b)
    | _ -> raise @@ TypingError (ExpectedFunction (f, f_ty))

  let typeof env ctx term = typeof_rec env ctx term
end
