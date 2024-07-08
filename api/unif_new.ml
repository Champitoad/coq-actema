(** Due to the use of union find data-structures, we have to use mutable 
    state in this module. Fortunately this mutability should not escape 
    this file. *)

open Utils.Pervasive
open Lang

(* Abbreviations for modules used in this file. *)
module HT = FVarId.Hashtbl
module UF = Utils.UnionFind.Make (FVarId)
module FVarGraph = Graph.Imperative.Digraph.Concrete (FVarId)

(***********************************************************************************)
(** Pre-substitutions. *)
(***********************************************************************************)

type sitem = SRigid | SFlex | SBound of Term.t [@@deriving show]

let print_uf fmt uf =
  let bindings =
    uf |> UF.domain
    |> List.filter_map (fun fvar ->
           let repr = UF.find uf fvar in
           if not @@ FVarId.equal fvar repr
           then
             Some
               (Format.sprintf "%s -> %s" (FVarId.show fvar) (FVarId.show repr))
           else None)
  in
  let classes = uf |> UF.classes |> List.map (List.to_string FVarId.show) in
  Format.fprintf fmt "[%s] ### [%s]"
    (String.concat ", " bindings)
    (String.concat ", " classes)

let print_table fmt tbl =
  let bindings =
    tbl |> HT.to_seq |> List.of_seq
    |> List.map (fun (fvar, item) ->
           Format.sprintf "%s := %s" (FVarId.show fvar) (show_sitem item))
  in
  Format.fprintf fmt "[%s]" (String.concat ", " bindings)

let show_deps forbidden_deps context deps : string =
  let module Attribs = struct
    include FVarGraph

    let graph_attributes _ = []
    let default_vertex_attributes _ = []

    let vertex_name var =
      match Context.find var context with
      | None -> "###"
      | Some entry -> begin
          match entry.binder with
          | Named name -> Name.show name
          | Anonymous -> "_"
        end

    let vertex_attributes _ = []
    let get_subgraph _ = None
    let default_edge_attributes _ = []

    let edge_attributes (edge : FVarGraph.edge) =
      let v1, v2 = edge in
      if List.mem (v2, v1) forbidden_deps then [ `Style `Dashed ] else []
  end in
  let module Dot = Graph.Graphviz.Dot (Attribs) in
  Format.asprintf "%a" Dot.fprint_graph deps

(** A pre-substitution keeps track of the unification state.
    
    Note that only top-level free variables (i.e. variables which are
    in the context passed to [unify]) are unifiable. Other variables may appear in 
    subterms, but they are treated as rigid variables and do not appear in the substitution.
*)
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
    tbl : sitem HT.t [@printer print_table]
  }
[@@deriving show]

let is_rigid presubst fvar =
  match HT.find_opt presubst.tbl fvar with Some SRigid -> true | _ -> false

let is_bound presubst fvar =
  match HT.find_opt presubst.tbl fvar with
  | Some (SBound _) -> true
  | _ -> false

let is_flex presubst fvar =
  match HT.find_opt presubst.tbl fvar with Some SFlex -> true | _ -> false

let get_bound presubst fvar : Term.t =
  match HT.find presubst.tbl fvar with SBound t -> t | _ -> assert false

(** [unify_cond env context presubst fvar term] checks whether we are allowed to instantiate
    the variable [fvar] with [term]. This does *not* however unify the types of [fvar] and [term].
    
    Precondition : [fvar] is the representative of its union-find class. *)
let unify_cond env context presubst fvar term : bool =
  let free_vars = Term.free_vars term in
  (* [fvar] has to be in the domain of [presubst] and be flex. *)
  is_flex presubst fvar
  (* All the free variables of [term] have to be in the domain of [subst]. *)
  && List.for_all (HT.mem presubst.tbl) free_vars
  (* Check [fvar] is not free in [term] (i.e. perform an occur-check).  *)
  && List.for_all (not <<< FVarId.equal fvar) free_vars

exception UnifFail

(** [unify_rec env context presubst t1 t2] performs syntactic unification on the terms [t1] and [t2],
    updating a pre-substitution [presubst] along the way.
    This does not check for cycles : it only performs occur-checks. 

    A note on free variables :
    - [presubst] contains only the top-level free variables, both in [presubst.tbl]
      and [presubst.uf].
    - [context] contains all free variables, including those that are not in scope at the top level.
    
    @raise UnifFail if [t1] and [t2] are not unifiable. *)
let rec unify_rec env context presubst ((t1, t2) : Term.t * Term.t) : unit =
  (*Format.printf "Unifying\n%s\n=?=\n%s\n"
    (Notation.term_to_string env ~ctx:context t1)
    (Notation.term_to_string env ~ctx:context t2);*)
  match (t1, t2) with
  (*************************************************************************)
  (* Trivial cases. *)
  (* The same free variable. This works even if these are not in the domain of [presubst]. *)
  | FVar v1, FVar v2 when FVarId.equal v1 v2 -> ()
  (* Free variables which are not in the domain of [presubst]. *)
  | FVar v, _ when not @@ UF.mem presubst.uf v -> raise UnifFail
  | _, FVar v when not @@ UF.mem presubst.uf v -> raise UnifFail
  (* Same sort. *)
  | Sort s1, Sort s2 when s1 = s2 -> ()
  (* Same constant. *)
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
      HT.replace presubst.tbl v (SBound t)
  | t, FVar v when unify_cond env context presubst v t ->
      (* Unify the types of [v] and [t]. *)
      unify_types env context presubst (Term.mkFVar v, t);
      (* Extend the substitution with a mapping [v --> SBound t]. *)
      HT.replace presubst.tbl v (SBound t)
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

(*presubst.tbl |> HT.to_seq |> List.of_seq
  |> List.filter_map (function v, SBound term -> Some (v, term) | _ -> None)*)

(** Normalize a presubstitution, i.e. replace every binding [v -> sitem] 
    by a binding [v -> sitem'] where [sitem'] is the item associated to 
    the representative of [v] in the union-find. *)
let normalize_presubst presubst : unit =
  let vars = UF.domain presubst.uf in
  List.iter
    begin
      fun v ->
        let repr = UF.find presubst.uf v in
        let sitem = HT.find presubst.tbl repr in
        HT.replace presubst.tbl v sitem
    end
    vars

(** Precondition : [presubst] is normalized. *)
let compute_dependencies forbidden_deps presubst : FVarGraph.t =
  (* Start from the empty graph. *)
  let deps = FVarGraph.create () in
  (* Add a vertex for each variable. *)
  List.iter (FVarGraph.add_vertex deps) @@ UF.domain presubst.uf;
  (* Add an edge [v2 --> v1] for each forbidden dependency (v1, v2). *)
  List.iter (fun (v1, v2) -> FVarGraph.add_edge deps v2 v1) forbidden_deps;
  (* Add edges for each binding [v --> SBound term] of the substitution. *)
  HT.iter
    begin
      fun v sitem ->
        match sitem with
        | SBound term ->
            (* Add an edge v -> v' for each free variable v' of [term]. *)
            List.iter (fun v' -> FVarGraph.add_edge deps v v')
            @@ Term.free_vars term
        | _ -> ()
    end
    presubst.tbl;
  deps

(***********************************************************************************)
(** Actual substitutions. *)
(***********************************************************************************)

let print_map fmt map =
  let bindings =
    FVarId.Map.bindings map
    |> List.map (fun (fvar, item) ->
           Format.sprintf "(%s, %s)" (FVarId.show fvar) (show_sitem item))
  in
  Format.fprintf fmt "[%s]" (String.concat "," bindings)

(** Substitutions are immutable. *)
type subst = { map : sitem FVarId.Map.t [@printer print_map] } [@@deriving show]

(** Temporary. *)
let convert_sitem__ (sitem : sitem) : Unif.sitem =
  match sitem with
  | SFlex -> SFlex
  | SRigid -> SRigid
  | SBound term -> SBound term

(** Temporary. *)
let convert_subst__ (subst : subst) : Unif.subst =
  Unif.{ map = FVarId.Map.map convert_sitem__ subst.map }

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

(***********************************************************************************)
(** Putting it all together. *)
(***********************************************************************************)

(** Convert a [presubst] to a [subst]. 
    This assumes the presubstitution is normalized. 
*)
let export_presubst presubst deps : subst =
  (* Get a topological sort of the dependency graph. *)
  let module Topo = Graph.Topological.Make (FVarGraph) in
  let sort = Topo.fold (fun v acc -> v :: acc) deps [] in
  let sort = List.rev sort in
  (* Precompute the index of each variable in the sort. *)
  let index =
    HT.of_seq @@ List.to_seq @@ List.mapi (fun i var -> (var, i)) sort
  in

  (* Make sure each edge in the dependency graph goes from left to right in the sort. *)
  FVarGraph.iter_edges
    (fun v1 v2 -> assert (HT.(find index v1 < find index v2)))
    deps;

  (* For each variable, compute the rightmost aliased variable. *)
  let rightmost_bindings =
    let open Utils.Monad.List in
    (* Iterate over the equivalence classes. *)
    let* vars = UF.classes presubst.uf in
    (* Compute the rightmost variable in the equivalence class. *)
    let rightmost_var = argmax (HT.find index) vars in
    let* v = vars in
    return (v, rightmost_var)
  in
  let rightmost = HT.of_seq @@ List.to_seq rightmost_bindings in

  (* Build the substitution. *)
  let map =
    HT.fold
      begin
        fun var sitem map ->
          let rightmost_var = HT.find rightmost var in
          match sitem with
          (* This variable is aliased but not substituted by a term :
             replace it by its rightmost alias. *)
          | SFlex when not @@ FVarId.equal rightmost_var var ->
              FVarId.Map.add var (SBound (Term.mkFVar rightmost_var)) map
          (* Otherwise simply keep the binding as is. *)
          | _ -> FVarId.Map.add var sitem map
      end
      presubst.tbl FVarId.Map.empty
  in
  { map }

let unify env context ?(rigid_fvars = []) ?(forbidden_deps = []) t1 t2 :
    subst option =
  (*Format.printf "***************************************\n";
    Format.printf "Context :\n%s\n" @@ Context.show context;
    Format.printf "Terms :\n%s\n=?=\n%s\n"
      (Notation.term_to_string env ~ctx:context t1)
      (Notation.term_to_string env ~ctx:context t2);*)

  (* Create the initial presubstitution. *)
  let flex_fvars =
    FVarId.Set.(
      to_list @@ diff (of_list @@ Context.domain context) (of_list rigid_fvars))
  in
  let bindings =
    List.map (fun fvar -> (fvar, SRigid)) rigid_fvars
    @ List.map (fun fvar -> (fvar, SFlex)) flex_fvars
  in
  let presubst =
    { tbl = HT.of_seq @@ List.to_seq bindings
    ; uf = UF.of_list @@ Context.domain context
    }
  in

  (* Compute the solution. *)
  try
    unify_rec env context presubst (t1, t2);
    (*Format.printf "After unify_rec :\n%s\n" @@ show_presubst presubst;*)
    (* The next steps assume [presubst] is normalized. *)
    normalize_presubst presubst;
    (*Format.printf "After normalize :\n%s\n" @@ show_presubst presubst;*)
    (* Compute the dependency graph. *)
    let deps = compute_dependencies forbidden_deps presubst in
    (*Out_channel.with_open_text
        "/home/mathis/Documents/work/coq-actema/graph.dot"
      @@ fun file ->
      Out_channel.output_string file @@ show_deps forbidden_deps context deps;*)
    (* Check the dependency graph is acyclic. *)
    let module Dfs = Graph.Traverse.Dfs (FVarGraph) in
    if Dfs.has_cycle deps then raise UnifFail;
    (* Convert the presubstitution to a substitution.
       This is where we resolve aliasing issues. *)
    let subst = export_presubst presubst deps in
    (*Format.printf "After export_presubst :\n%s\n" @@ show_subst subst;*)
    (* Don't forget to close the substitution. *)
    Some (close subst)
  with UnifFail -> None
