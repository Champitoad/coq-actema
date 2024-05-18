(*open Utils
  open Lang

  (** A simple option monad used in this file. *)
  module OptionMonad = struct
    let return x = Some x
    let fail = None
    let ( >>= ) = Option.bind
    let ( let* ) = Option.bind
    let ( let+ ) = Option.map

    (** Monadic fold. *)
    let foldM (f : 'acc -> 'a -> 'acc option) (acc : 'acc) (xs : 'a list) :
        'acc option =
      List.fold_left
        (fun acc x -> match acc with None -> None | Some acc -> f acc x)
        (Some acc) xs
  end

  module Subst = struct
    type t

    val empty : t
    val is_empty : t -> bool
    val is_bound : int -> t -> bool
    val bind : int -> Term.t -> t -> t
    val fetch : int -> t -> t option
    val apply : t -> Term.t -> Term.t

    (** Can also lower if int < 0. *)
    val lift : int -> t -> t

    (** This assumes that [n] --> [t] implies that [free_vars t > n]. *)
    val close : t -> t
  end

  let rec unify_rec depth subst ((t1, t2) : Term.t * Term.t) : Subst.t option =
    (** Can we bind the variable [Var n] to the term [t] ? *)
    let bind_cond n t =
      let free_t = TermUtils.free_vars t in

      (* [n] has to exist in the substitution and be a flex variable. *)
      Subst.is_flex (n - depth) subst &&
      (* [t] should not use any variables defined below [n],
         i.e. [n] all the free variables of [t] should be in the scope [n] has access to.

         For instance when trying to unify the following
           [fun x : nat => ?n] with [fun y : nat => y + 42] where [?n] is Sflex
         we should not map [?n] to [y + 42] (because [y] does not exist in the scope [?n]
         has access to), and we should fail instead.

         Note that this also prevents [n] from occuring in the free variables of [t].
      *)
      IntSet.min_elt free_t > n
    in

    let open OptionMonad in
    match (t1, t2) with
    (* For simple cases we are done. *)
    | Sort `Prop, Sort `Prop -> return subst
    | Sort `Type, Sort `Type -> return subst
    | Cst c1, Cst c2 when Name.equal c1 c2 -> return subst
    | Var n1, Var n2 when n1 = n2 -> return subst
    (* If one of [t1] or [t2] is a flex variable, we add a mapping in the substitution. *)
    | Var n1, t2 when bind_cond n1 t2 -> return @@ Subst.bind n1 t2 subst
    | t1, Var n2 when bind_cond n2 t1 -> return @@ Subst.bind n2 t1 subst
    (* If one of [t1] or [t2] is a bound variable, we substitute it and recurse. *)
    | Var n1, t2 when Subst.is_bound n1 subst ->
        unify env ctx subst (Subst.fetch n1 subst, t2)
    | t1, Var n2 when Subst.is_bound n2 subst ->
        unify env ctx subst (t1, Subst.fetch n2 subst)
    (* Otherwise we recurse on substerms of [t1] and [t2]. *)
    | App (f1, args1), App (f2, args2) when List.length args1 = List.length args2
      ->
        foldM (unify env ctx) subst [ (f1, f2) ]
    | Arrow (a1, b1), Arrow (a2, b2) ->
        let* subst = unify env ctx subst (a1, a2) in
        let* subst = unify env ctx subst (b1, b2) in
        return subst
    | Lambda (x1, ty1, body1), Lambda (x2, ty2, body2) ->
        (* First unify the types. *)
        let* subst = unify env ctx subst (ty1, ty2) in
        (* Then unify the bodies. We take care to extend the context and substitution. *)
        let* subst =
          unify env (Context.push x1 ty2 ctx) (Subst.push subst) (body1, body2)
        in
        (* Return the resulting substitution. *)
        return subst
    (* We could not unify [t1] and [t2] : fail. *)
    | _ -> fail
*)
