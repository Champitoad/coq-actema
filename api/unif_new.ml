(** Due to the use of union find data-structures, we have to use mutable 
    state in this module. Fortunately this mutability should not escape 
    this file. *)

open Utils.Pervasive
open Lang
module UF = Utils.UnionFind.Make (FVarId)

type sitem = SRigid | SFlex | SBound of Term.t [@@deriving show]

let print_uf fmt uf =
  let bindings =
    uf |> UF.domain
    |> List.map (fun fvar ->
           let repr = UF.find uf fvar in
           if not @@ FVarId.equal fvar repr
           then Format.sprintf "%s -> %s" (FVarId.show fvar) (FVarId.show repr)
           else "")
  in
  Format.fprintf fmt "[%s]" (String.concat "," bindings)

let print_table fmt tbl =
  let bindings =
    tbl |> FVarId.Hashtbl.to_seq |> List.of_seq
    |> List.map (fun (fvar, item) ->
           Format.sprintf "%s := %s" (FVarId.show fvar) (show_sitem item))
  in
  Format.fprintf fmt "[%s]" (String.concat "," bindings)

(*let print_deps fmt deps =
  let edges = FVarGraph.fold_edges (fun i j acc -> (i, j) :: acc) deps [] in
  let bindings =
    List.map
      (fun (i, j) -> Format.sprintf "%s --> %s" (FVarId.show i) (FVarId.show j))
      edges
  in
  Format.fprintf fmt "[%s]" (String.concat "," bindings)*)

(** Substitutions are updated in place. *)
type subst =
  { (* The underlying union-find datastructure on free variables
       that keeps track of which variables are aliased.
       This is mutable. *)
    uf : UF.t [@printer print_uf]
  ; (* The mapping from free variables to sitems. As an invariant,
       all aliased free variables should point to the same sitem.

       Since the union-find is already mutable, we use a hashtable here
       rather than a persistent map for slightly better performance. *)
    tbl : sitem FVarId.Hashtbl.t [@printer print_table]
  }
[@@deriving show]

let get_sitem subst fvar = FVarId.Hashtbl.find_opt subst.tbl fvar

let is_rigid subst fvar =
  match FVarId.Hashtbl.find_opt subst.tbl fvar with
  | Some SRigid -> true
  | _ -> false

let is_bound subst fvar =
  match FVarId.Hashtbl.find_opt subst.tbl fvar with
  | Some (SBound _) -> true
  | _ -> false

let is_flex subst fvar =
  match FVarId.Hashtbl.find_opt subst.tbl fvar with
  | Some SFlex -> true
  | _ -> false

let get_bound fvar subst : Term.t =
  match FVarId.Hashtbl.find subst.tbl fvar with
  | SBound t -> t
  | _ -> assert false

(** The [repeat] flag controls what we do when we substitute a bound variable. *)
(*let rec apply_rec ~repeat subst (term : Term.t) : Term.t =
    match term with
    | Cst _ | Sort _ | BVar _ -> term
    | FVar v -> begin
        match FVarId.Map.find_opt v subst.map with
        | Some (SBound t) -> if repeat then apply_rec ~repeat subst t else t
        | _ -> term
      end
    | Lambda (_, x, ty, body) ->
        let ty = apply_rec ~repeat subst ty in
        let body = apply_rec ~repeat subst body in
        Term.mkLambda x ty body
    | Prod (_, x, ty, body) ->
        let ty = apply_rec ~repeat subst ty in
        let body = apply_rec ~repeat subst body in
        Term.mkProd x ty body
    | App (_, f, args) ->
        let f = apply_rec ~repeat subst f in
        let args = List.map (apply_rec ~repeat subst) args in
        Term.mkApps f args

  let apply subst term : Term.t = apply_rec ~repeat:false subst term

  (** This assumes that the substitution is acyclic. *)
  let close subst : subst =
    let map =
      FVarId.Map.mapi
        begin
          fun var sitem ->
            match sitem with
            | SRigid -> SRigid
            | SFlex -> SFlex
            | SBound term -> SBound (apply_rec ~repeat:true subst term)
        end
        subst.map
    in
    { map }

  (** [unify_cond env context subst fvar term] checks whether we are allowed to instantiate
      the variable [fvar] with [term]. This does *not* however unify the types of [fvar] and [term]. *)
  let unify_cond env context subst fvar term : bool =
    let free_vars = Term.free_vars term in
    (* [fvar] has to be in the domain of [subst] and be flex. *)
    FVarId.Map.find_opt fvar subst.map = Some SFlex
    (* All the free variables of [term] have to be in the domain of [subst]. *)
    && List.for_all (fun tvar -> FVarId.Map.mem tvar subst.map) free_vars
    (* Check [fvar] is not free in [term] (this is known as an occur-check).  *)
    && (not @@ List.mem fvar free_vars)

  (** [unify_rec subst t1 t2] performs syntactic unification on the terms [t1] and [t2],
      starting with a substitution [subst].
      This doesn't check for cycles, but instead returns a lazy list of all unifiers. *)
  let rec unify_rec env context subst ((t1, t2) : Term.t * Term.t) : subst Seq.t =
    let open Utils.Monad.Seq in
    match (t1, t2) with
    (*************************************************************************)
    (* Trivial cases. *)
    | FVar v1, FVar v2 when FVarId.equal v1 v2 -> return subst
    | Sort s1, Sort s2 when s1 = s2 -> return subst
    | Cst c1, Cst c2 when Name.equal c1 c2 -> return subst
    (*************************************************************************)
    (* Expand a variable that is in the substitution. *)
    | FVar v, t when is_bound subst v ->
        unify_rec env context subst (get_bound v subst, t)
    | t, FVar v when is_bound subst v ->
        unify_rec env context subst (get_bound v subst, t)
    (*************************************************************************)
    (* Extend the substitution. *)
    | FVar v1, FVar v2
      when unify_cond env context subst v1 (Term.mkFVar v2)
           && unify_cond env context subst v2 (Term.mkFVar v1) ->
        (* Unify the types of [v1] and [v2]. *)
        let* subst =
          unify_types env context subst (Term.mkFVar v1, Term.mkFVar v2)
        in
        (* This is a choice point : we try both [v1 --> v2] and [v2 --> v1].
           Since we are using lazy lists this simulates backtracking. *)
        List.to_seq
          [ { map = FVarId.Map.add v1 (SBound (Term.mkFVar v2)) subst.map }
          ; { map = FVarId.Map.add v2 (SBound (Term.mkFVar v1)) subst.map }
          ]
    | FVar v, t when unify_cond env context subst v t ->
        (* Unify the types of [v] and [t]. *)
        let* subst = unify_types env context subst (Term.mkFVar v, t) in
        (* Extend the substitution with a mapping [v --> SBound t]. *)
        return { map = FVarId.Map.add v (SBound t) subst.map }
    | t, FVar v when unify_cond env context subst v t ->
        (* Unify the types of [v] and [t]. *)
        let* subst = unify_types env context subst (Term.mkFVar v, t) in
        (* Extend the substitution with a mapping [v --> SBound t]. *)
        return { map = FVarId.Map.add v (SBound t) subst.map }
    (*************************************************************************)
    (* Recursive cases. *)
    | App (_, f1, args1), App (_, f2, args2)
      when List.length args1 = List.length args2 ->
        foldM (unify_rec env context) subst
        @@ List.combine (f1 :: args1) (f2 :: args2)
    | Lambda (_, x1, ty1, body1), Lambda (_, x2, ty2, body2)
    | Prod (_, x1, ty1, body1), Prod (_, x2, ty2, body2) ->
        (* Unify the types. *)
        let* subst = unify_rec env context subst (ty1, ty2) in
        (* Unify the bodies. We extend the context here. *)
        let fvar, new_context = Context.add_fresh x1 ty1 context in
        let new_body1 = Term.instantiate fvar body1 in
        let new_body2 = Term.instantiate fvar body2 in
        unify_rec env new_context subst (new_body1, new_body2)
    (*************************************************************************)
    (* We failed to unify. *)
    | _ -> Seq.empty

  (** Same as [unify_rec], but unififes the types of the terms instead of unifying the terms. *)
  and unify_types env context subst (t1, t2) : subst Seq.t =
    let ty1 = TermUtils.typeof env context t1 in
    let ty2 = TermUtils.typeof env context t2 in
    unify_rec env context subst (ty1, ty2)

  let subst_bindings subst : (FVarId.t * Term.t) list =
    subst.map |> FVarId.Map.bindings
    |> List.filter_map (function v, SBound term -> Some (v, term) | _ -> None)

  let compute_dependencies forbidden_deps subst : FVarGraph.t =
    (* Start from the empty graph. *)
    let deps = FVarGraph.empty in
    (* Add an edge [v2 --> v1] for each forbidden dependency (v1, v2). *)
    let deps =
      List.fold_left
        (fun deps (v1, v2) -> FVarGraph.add_edge deps v2 v1)
        deps forbidden_deps
    in
    (* Add edges for each binding [v --> SBound term] of the substitution. *)
    let deps =
      List.fold_left
        begin
          fun deps (v, term) ->
            (* Add an edge v -> v' for each free variable v' of [term]. *)
            List.fold_left
              (fun deps v' -> FVarGraph.add_edge deps v v')
              deps (Term.free_vars term)
        end
        deps (subst_bindings subst)
    in
    deps

  let unify env context ?(rigid_fvars = []) ?(forbidden_deps = []) t1 t2 :
      subst option =
    (* Create the initial substitution's mapping. *)
    let flex_fvars =
      FVarId.Set.to_list
      @@ FVarId.Set.diff
           (FVarId.Set.of_list @@ Context.domain context)
           (FVarId.Set.of_list rigid_fvars)
    in
    let bindings =
      List.map (fun fvar -> (fvar, SRigid)) rigid_fvars
      @ List.map (fun fvar -> (fvar, SFlex)) flex_fvars
    in
    let subst = { map = FVarId.Map.of_list bindings } in

    (* Compute all solutions - acyclic or not - *on demand* using a lazy list. *)
    let solutions = unify_rec env context subst (t1, t2) in

    (* Find the first acyclic solution. *)
    Seq.find_map
      begin
        fun subst ->
          let deps = compute_dependencies forbidden_deps subst in
          let module Dfs = Graph.Traverse.Dfs (FVarGraph) in
          if Dfs.has_cycle deps then None else Some (close subst)
      end
      solutions
*)
