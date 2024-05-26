open Utils.Pervasive
open Api
open Lang
module IntGraph = Graph.Persistent.Digraph.Concrete (Stdlib.Int)

type sitem = SRigid | SFlex | SBound of Term.t [@@deriving show]

let print_mapping fmt map =
  let bindings =
    IntMap.bindings map
    |> List.map (fun (var, item) ->
           Format.sprintf "(%d, %s)" var (show_sitem item))
  in
  Format.fprintf fmt "[%s]" (String.concat "," bindings)

let print_deps fmt deps =
  let edges = IntGraph.fold_edges (fun i j acc -> (i, j) :: acc) deps [] in
  let bindings =
    List.map (fun (i, j) -> Format.sprintf "%d --> %d" i j) edges
  in
  Format.fprintf fmt "[%s]" (String.concat "," bindings)

type subst =
  { n_free_1 : int
  ; n_free_2 : int
  ; context : Context.t
  ; mapping : sitem IntMap.t [@printer print_mapping]
  ; deps : IntGraph.t [@printer print_deps]
  }
[@@deriving show]

(** [unify_cond depth subst var term] checks whether we can add the mapping [var --> term]
    to [subst].
    [var] and [term] both live at level [depth], whereas [subst] always lives at level [0]. *)
let unify_cond depth env subst var term : bool =
  let fvars = TermUtils.free_vars term in
  (* [var] has to be a free variable. *)
  var >= depth
  (* [var] has to be an Sflex variable. *)
  && IntMap.find (var - depth) subst.mapping = SFlex
  (* [term] must only use variables that are free in the original [t1] or [t2]. *)
  && (IntSet.is_empty fvars || IntSet.min_elt fvars >= depth)
  (* [var] and [term] must have the same type. *)
  && snd @@ Option.get @@ Context.get (var - depth) subst.context
     = Typing.typeof ~context:subst.context env term

(** [var] lives at level [depth], whereas [subst] always lives at level [0]. *)
let expand_cond depth subst var : bool =
  (* [var] has to be a free variable. *)
  var >= depth
  (* [var] has to be bound in [subst]. *)
  && match IntMap.find var subst.mapping with SBound _ -> true | _ -> false

(** [unify_rec depth subst (t1, t2)] performs syntactic unification on the terms [t1] and [t2], 
    starting with a substitution [subst]. Initially [depth] should be equal to [0]. 
    This does not build the [deps] graph of the substitution, 
    and does not check for cycles. *)
let rec unify_rec depth env (subst : subst) ((t1, t2) : Term.t * Term.t) :
    subst Seq.t =
  let open Utils.Monad.Seq in
  (* Apply the subsitution to [v]. *)
  let do_expand v t : subst Seq.t =
    match IntMap.find (v - depth) subst.mapping with
    | SBound t' -> unify_rec depth env subst (t, t')
    | _ -> assert false
  in
  (* Extend the substitution in two separate ways :
     1. with a mapping [v1 --> v2]
     2. with a mapping [v2 --> v1] *)
  let do_unify_vars v1 v2 : subst Seq.t =
    (* Lower [v1] and [v2] from level [depth] to level [0]. *)
    let v1 = v1 - depth in
    let v2 = v2 - depth in
    (* This is a choice point : we try both [v1 --> v2] and [v2 --> v1].
       Since we are using lazy lists this simulates backtracking. *)
    List.to_seq
      [ { subst with
          mapping = IntMap.add v1 (SBound (Term.mkVar v2)) subst.mapping
        }
      ; { subst with
          mapping = IntMap.add v2 (SBound (Term.mkVar v1)) subst.mapping
        }
      ]
  in
  (* Extend the substitution with a mapping [v --> SBound t]. *)
  let do_unify v t : subst Seq.t =
    (* Lower [v] and [t] from level [depth] to level [0]. *)
    let v = v - depth in
    let t = TermUtils.lift_free (-depth) t in
    (* Extend the substitution's mapping. *)
    return { subst with mapping = IntMap.add v (SBound t) subst.mapping }
  in
  match (t1, t2) with
  (* Trivial cases. *)
  | Var v1, Var v2 when v1 = v2 -> return subst
  | Sort s1, Sort s2 when s1 = s2 -> return subst
  | Cst c1, Cst c2 when Name.equal c1 c2 -> return subst
  (* Expand a variable that is in the substitution. *)
  | Var v, t when expand_cond depth subst v -> do_expand v t
  | t, Var v when expand_cond depth subst v -> do_expand v t
  (* Add a mapping to the substitution. *)
  | Var v1, Var v2
    when unify_cond depth env subst v1 (Term.mkVar v2)
         && unify_cond depth env subst v2 (Term.mkVar v1) ->
      do_unify_vars v1 v2
  | Var v, t when unify_cond depth env subst v t -> do_unify v t
  | t, Var v when unify_cond depth env subst v t -> do_unify v t
  (* Recursive cases. *)
  | App (f1, args1), App (f2, args2) when List.length args1 = List.length args2
    ->
      foldM (unify_rec depth env) subst
      @@ List.combine (f1 :: args1) (f2 :: args2)
  | Lambda (x1, ty1, body1), Lambda (x2, ty2, body2)
  | Prod (x1, ty1, body1), Prod (x2, ty2, body2) ->
      let* subst = unify_rec depth env subst (ty1, ty2) in
      let* subst = unify_rec (depth + 1) env subst (body1, body2) in
      return subst
  | Arrow (a1, b1), Arrow (a2, b2) ->
      let* subst = unify_rec depth env subst (a1, a2) in
      let* subst = unify_rec depth env subst (b1, b2) in
      return subst
  (* We failed to unify. *)
  | _ -> Seq.empty

(** [range low high] returns the list [low; low + 1; ...; high - 1] ([low] included, [high] excluded).
    Returns an empty list if [low > high]. *)
let range low high =
  if low > high then [] else List.init (high - low) (fun i -> i + low)

(** [build_deps subst] returns a substitution equivalent to [subst], 
    but with the [deps] graph computed. 
    This only build the [deps] graph : it does not check for cycles. *)
let build_deps (subst : subst) : subst =
  let n1 = subst.n_free_1 in
  let n2 = subst.n_free_2 in
  let all_vars = List.init (n1 + n2) Fun.id in
  (* Start from the empty graph. *)
  let deps = IntGraph.empty in
  (* Add a vertex for each free variable. *)
  let deps = List.fold_left IntGraph.add_vertex deps all_vars in
  (* Add an edge [i --> i-1] for each variable free in [t1] or [t2]. *)
  let indices =
    range 1 subst.n_free_1
    @ range (subst.n_free_1 + 1) (subst.n_free_1 + subst.n_free_2)
  in
  let deps =
    List.fold_left (fun deps i -> IntGraph.add_edge deps i (i - 1)) deps indices
  in
  (* Add an edge for each element [i --> Sbound term] of the substitution. *)
  let deps =
    List.fold_left
      begin
        fun deps i ->
          (* Check if i is bound in [subst]. *)
          match IntMap.find i subst.mapping with
          | SBound term ->
              (* Add an edge i -> j for each free variable j of [term]. *)
              IntSet.fold
                (fun j deps -> IntGraph.add_edge deps i j)
                (TermUtils.free_vars term) deps
          | _ -> deps
      end
      deps all_vars
  in
  { subst with deps }

let unify env (sitems1, ctx1, t1) (sitems2, ctx2, t2) : subst Seq.t =
  assert (List.length sitems1 = Context.size ctx1);
  assert (List.length sitems2 = Context.size ctx2);

  (* Create the initial substitution. *)
  let n_free_1 = List.length sitems1 in
  let n_free_2 = List.length sitems2 in
  let indices = range 0 (n_free_1 + n_free_2) in
  let mapping = IntMap.of_list @@ List.combine indices (sitems1 @ sitems2) in
  let subst =
    { n_free_1
    ; n_free_2
    ; context = Context.stack ctx1 ctx2
    ; mapping
    ; deps = IntGraph.empty
    }
  in

  (* Compute all solutions (acyclic or not). *)
  let solutions = unify_rec 0 env subst (t1, TermUtils.lift_free n_free_1 t2) in

  (* Filter out the cyclic solutions. This is lazy. *)
  Seq.filter_map
    begin
      fun subst ->
        let subst = build_deps subst in
        let module Dfs = Graph.Traverse.Dfs (IntGraph) in
        if Dfs.has_cycle subst.deps then None else Some subst
    end
    solutions

(** The [repeat] flag controls what we do when we substitute a bound variable. *)
let rec apply_rec ~repeat depth subst (term : Term.t) : Term.t =
  match term with
  | Cst _ | Sort _ -> term
  | Var v -> begin
      match IntMap.find_opt (v - depth) subst.mapping with
      | Some (SBound t) ->
          let t = TermUtils.lift_free depth t in
          if repeat then apply_rec ~repeat depth subst t else t
      | _ -> term
    end
  | Lambda (x, ty, body) ->
      let ty = apply_rec ~repeat depth subst ty in
      let body = apply_rec ~repeat (depth + 1) subst body in
      Term.mkLambda x ty body
  | Prod (x, ty, body) ->
      let ty = apply_rec ~repeat depth subst ty in
      let body = apply_rec ~repeat (depth + 1) subst body in
      Term.mkProd x ty body
  | Arrow (t1, t2) ->
      let t1 = apply_rec ~repeat depth subst t1 in
      let t2 = apply_rec ~repeat depth subst t2 in
      Term.mkArrow t1 t2
  | App (f, args) ->
      let f = apply_rec ~repeat depth subst f in
      let args = List.map (apply_rec ~repeat depth subst) args in
      Term.mkApps f args

let apply ~repeat subst term = apply_rec ~repeat 0 subst term

let close subst =
  let mapping =
    IntMap.mapi
      begin
        fun var sitem ->
          match sitem with
          | SRigid -> SRigid
          | SFlex -> SFlex
          | SBound term -> SBound (apply ~repeat:true subst term)
      end
      subst.mapping
  in

  { subst with mapping }
