(** Due to the use of union find data-structures, we have to use mutable 
    state in this module. Fortunately this mutability should not escape 
    this file. *)

open Utils.Pervasive
open Lang
module UF = Utils.UnionFind.Make (FVarId)
module FVarGraph = Graph.Imperative.Digraph.Concrete (FVarId)

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

type presubst =
  { (* The underlying union-find datastructure on free variables
       that keeps track of which variables are aliased.
       This is mutable. *)
    uf : UF.t [@printer print_uf]
  ; (* The mapping from free variables to sitems.
       When a free variables is aliased its sitem is meaningless :
       you should use the sitem of its representative instead.

       Since the union-find is already mutable, we use a hashtable here
       rather than a persistent map for slightly better performance. *)
    tbl : sitem FVarId.Hashtbl.t [@printer print_table]
  }
[@@deriving show]

let is_rigid presubst fvar =
  match FVarId.Hashtbl.find_opt presubst.tbl fvar with
  | Some SRigid -> true
  | _ -> false

let is_bound presubst fvar =
  match FVarId.Hashtbl.find_opt presubst.tbl fvar with
  | Some (SBound _) -> true
  | _ -> false

let is_flex presubst fvar =
  match FVarId.Hashtbl.find_opt presubst.tbl fvar with
  | Some SFlex -> true
  | _ -> false

let get_bound presubst fvar : Term.t =
  match FVarId.Hashtbl.find presubst.tbl fvar with
  | SBound t -> t
  | _ -> assert false

(** [unify_cond env context presubst fvar term] checks whether we are allowed to instantiate
    the variable [fvar] with [term]. This does *not* however unify the types of [fvar] and [term].
    
    Precondition : [fvar] is the representative of its union-find class. *)
let unify_cond env context presubst fvar term : bool =
  let free_vars = Term.free_vars term in
  (* [fvar] has to be in the domain of [subst] and be flex. *)
  is_flex presubst fvar
  (* All the free variables of [term] have to be in the domain of [subst]. *)
  && List.for_all (fun tvar -> FVarId.Hashtbl.mem presubst.tbl tvar) free_vars
  (* Check [fvar] is not free in [term] (i.e. perform an occur-check).  *)
  && List.for_all (not <<< UF.equiv presubst.uf fvar) free_vars

exception UnifFail

(** [unify_rec subst t1 t2] performs syntactic unification on the terms [t1] and [t2],
    starting with a substitution [subst].
    This does not check for cycles : it only performs occur-checks. 
    
    @raise UnifFail if [t1] and [t2] are not unifiable. *)
let rec unify_rec env context presubst ((t1, t2) : Term.t * Term.t) : unit =
  match (t1, t2) with
  (*************************************************************************)
  (* Trivial cases. *)
  | FVar v1, FVar v2 when FVarId.equal v1 v2 -> ()
  | Sort s1, Sort s2 when s1 = s2 -> ()
  | Cst c1, Cst c2 when Name.equal c1 c2 -> ()
  (*************************************************************************)
  (* Deal with aliased variables. *)
  | FVar v, t when not @@ UF.is_representative presubst.uf v ->
      unify_rec env context presubst (Term.mkFVar @@ UF.find presubst.uf v, t)
  | t, FVar v when not @@ UF.is_representative presubst.uf v ->
      unify_rec env context presubst (t, Term.mkFVar @@ UF.find presubst.uf v)
  (*************************************************************************)
  (* Substitute a variable that is bound in the substitution. *)
  | FVar v, t when is_bound presubst v ->
      unify_rec env context presubst (get_bound presubst v, t)
  | t, FVar v when is_bound presubst v ->
      unify_rec env context presubst (t, get_bound presubst v)
  (*************************************************************************)
  (* Alias two free variables. If one of them is rigid we don't alias them
     but instead extend the substitution (see next cases). *)
  | FVar v1, FVar v2 when is_flex presubst v1 && is_flex presubst v2 ->
      (* Unify the types of [v1] and [v2]. *)
      unify_types env context presubst (Term.mkFVar v1, Term.mkFVar v2);
      (* Merge the classes of [v1] and [v2] in the union-find. *)
      UF.union presubst.uf v1 v2
  (*************************************************************************)
  (* Extend the substitution. *)
  | FVar v, t when unify_cond env context presubst v t ->
      (* Unify the types of [v] and [t]. *)
      unify_types env context presubst (Term.mkFVar v, t);
      (* Extend the substitution with a mapping [v --> SBound t]. *)
      FVarId.Hashtbl.add presubst.tbl v (SBound t)
  | t, FVar v when unify_cond env context presubst v t ->
      (* Unify the types of [v] and [t]. *)
      unify_types env context presubst (Term.mkFVar v, t);
      (* Extend the substitution with a mapping [v --> SBound t]. *)
      FVarId.Hashtbl.add presubst.tbl v (SBound t)
  (*************************************************************************)
  (* Recursive cases. *)
  | App (_, f1, args1), App (_, f2, args2)
    when List.length args1 = List.length args2 ->
      List.iter (unify_rec env context presubst)
      @@ List.combine (f1 :: args1) (f2 :: args2)
  | Lambda (_, x1, ty1, body1), Lambda (_, x2, ty2, body2)
  | Prod (_, x1, ty1, body1), Prod (_, x2, ty2, body2) ->
      (* Unify the types. *)
      unify_rec env context presubst (ty1, ty2);
      (* Unify the bodies. We extend the context here. *)
      let fvar, new_context = Context.add_fresh x1 ty1 context in
      let new_body1 = Term.instantiate fvar body1 in
      let new_body2 = Term.instantiate fvar body2 in
      unify_rec env new_context presubst (new_body1, new_body2)
  (*************************************************************************)
  (* We failed to unify. *)
  | _ -> raise UnifFail

(** Same as [unify_rec], but unififes the types of the terms instead of unifying the terms. *)
and unify_types env context presubst (t1, t2) : unit =
  let ty1 = TermUtils.typeof env context t1 in
  let ty2 = TermUtils.typeof env context t2 in
  unify_rec env context presubst (ty1, ty2)

let subst_bindings presubst : (FVarId.t * Term.t) list =
  presubst.tbl |> FVarId.Hashtbl.to_seq |> List.of_seq
  |> List.filter_map (function
       | v, SBound term when UF.is_representative presubst.uf v -> Some (v, term)
       | _ -> None)

let compute_dependencies forbidden_deps subst : FVarGraph.t =
  (* Start from the empty graph. *)
  let deps = FVarGraph.create () in
  (* Add an edge [v2 --> v1] for each forbidden dependency (v1, v2). *)
  List.iter (fun (v1, v2) -> FVarGraph.add_edge deps v2 v1) forbidden_deps;
  (* Add edges for each binding [v --> SBound term] of the substitution
     where [v] is a representative. *)
  List.iter
    begin
      fun (v, term) ->
        (* Add an edge v -> v' for each free variable v' of [term]. *)
        List.iter (fun v' -> FVarGraph.add_edge deps v v')
        @@ Term.free_vars term
    end
  @@ subst_bindings subst;
  deps

(*let unify env context ?(rigid_fvars = []) ?(forbidden_deps = []) t1 t2 :
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
(***********************************************************************************)
(** Actual substitutions. *)
(***********************************************************************************)

(** substitutions are immutable. *)
type subst = { map : sitem FVarId.Map.t }

(** The [repeat] flag controls what we do when we substitute a bound variable. *)
let rec apply_rec ~repeat subst (term : Term.t) : Term.t =
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
