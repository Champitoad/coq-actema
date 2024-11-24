(* This module contains utility functions for Ltac2. 
   It is used mainly by DnD.v *)

From Ltac2 Require Import Ltac2.
Import Constr Constr.Unsafe.

(*** Smart constructor for [Rel]. *)
Ltac2 mk_rel (n : int) : constr := make (Rel n).

(** Smart constructor for [Var]. *)
Ltac2 mk_var (id : ident) : constr := make (Var id).

(*** Smart constructor for [Evar]. *)
Ltac2 mk_evar (ev : evar) : constr := make (Evar ev [| |]).
  
(** Smart constructor for [Lambda]. *)
Ltac2 mk_lambda (bind : binder) (body : constr) : constr := make (Lambda bind body).

(** Smart constructor for [Prod]. *)
Ltac2 mk_prod (bind : binder) (body : constr) : constr := make (Prod bind body).
  
(** Smart constructor for [App]. *)
Ltac2 mk_app (f : constr) (args : constr array) : constr := make (App f args).

(** [binder_name c] returns the name of the binder of [c]. *)
Ltac2 binder_name (c : constr) : ident option := 
  match kind c with 
  | Lambda binder _ => Constr.Binder.name binder 
  | Prod binder _ => Constr.Binder.name binder 
  | _ => None
  end.

(** [beta_root c] forces the beta reduction at the root of [c], if [c] is a beta redex.
   Otherwise it returns [c] unchanged. *)
Ltac2 beta_root (c : constr) : constr := 
  lazy_match! c with 
  | ?f ?x => 
    match kind f with 
    | Lambda _ body => substnl [ x ] 0 body
    | _ => c
    end
  | _ => c
  end.
  
(** [beta_equiv t1 t2] checks whether the terms [t1] and [t2] are beta equivalent. *)
Ltac2 beta_equiv (t1 : constr) (t2 : constr) : bool := 
  let t1 := Std.eval_cbv RedFlags.all t1 in 
  let t2 := Std.eval_cbv RedFlags.all t2 in 
  Constr.equal t1 t2.

(** [freh_evar basename type] creates a fresh evar with the type [type].
    Optionally [basename] can be used to indicate a prefered name for the evar
    (wich might be slightly modified to ensure freshness).
   
    The evar is added to the local context, and the name of the corresponding
    hypothesis is returned. *)
Ltac2 fresh_evar (id_opt : ident option) (type_opt : constr option) : ident := 
  (* Get the name. *)
  let id := 
    match id_opt with 
    | Some id => Fresh.in_goal id 
    | None => Fresh.in_goal @x
    end 
  in
  (* Get the type. *)
  let type := 
    match type_opt with 
    | Some type => type 
    | None => '(_ : Type) 
    end
  in 
  (* We have to use a trick to ensure the evar has the right name. 
     We create an identity function with the correct type and binder name : 
     this binder name will magically get chosen as the evar name. *)
  let binder := Constr.Binder.make (Some id) type in
  let my_lambda := mk_lambda binder (mk_rel 1) in
  (* Create the evar. *)
  epose ($my_lambda _ : $type) as $id ;
  hnf in $id ;
  id.
  
(** [abstract_ident ev c] replaces all occurences of the identifier [id] in [c]
    by a local (de Bruijn) variable, and binds this local variable with a lambda abstraction. 
   
    For instance : 
      [abstract_ident x (P x /\ A)] would give [fun x => P x /\ A]
      [abstract_ident y (P x /\ A)] would give [fun _ => P x /\ A]
*)
Ltac2 abstract_ident (id : ident) (c : constr) : constr :=
  (* First replace [id] by [Rel 0]. *)
  let body := closenl [ id ] 1 c in
  (* Create the binder. *)
  let type := Constr.type (mk_var id) in 
  let binder := Constr.Binder.make (Some id) type in
  (* Make the lambda abstraction. *)
  mk_lambda binder body.

(** [fun_to_forall f] returns a term beta-equivalent to [forall x, f x], 
    but when [f] is a lambda abstarction we take care to keep the binder name of [f] 
    and to beta reduce [f x]. *)
Ltac2 fun_to_forall (id : ident option) (f : constr) : constr :=   
  match kind f with 
  | Lambda binder body => 
    let binder := 
      match id with 
      | None => binder
      | Some id => Constr.Binder.make (Some id) (Constr.Binder.type binder) 
      end
    in
    mk_prod binder body
  | _ => '(forall x, $f x)
  end.

(** Exception raised when a subpath in a term is invalid. *)
Ltac2 Type exn ::= [ InvalidSubpath (constr, int list)].

(** [map_subterm f c sub] replaces the subterm [sc] of [c] at path [sub] with [f n sc],
    where [n] is the number of binders traversed along the path [sub]. *)
Ltac2 map_subterm (f : int -> constr -> constr) (c : constr) (sub : int list) : constr := 
  let rec loop n c sub :=   
    lazy_match! c with 
    (* Special case for exist. *)
    | ex ?body => 
      (* Here we reuse the same [sub] but instead go into the [body] function. *)
      let body := loop n body sub in '(ex $body)
    (* All other cases. *)
    | _ => 
      match kind c, sub with 
      (* Base case. *)
      | _, [] => f n c
      (* Lambda abstraction. *)
      | Lambda bind body, 0 :: sub => 
        let id := Constr.Binder.name bind in 
        let type := loop n (Constr.Binder.type bind) sub in 
        let bind := Constr.Binder.make id type in
        mk_lambda bind body
      | Lambda bind body, 1 :: sub => 
        let body := loop (Int.add n 1) body sub in
        mk_lambda bind body
      (* Product. *)
      | Prod bind body, 0 :: sub => 
        let id := Constr.Binder.name bind in 
        let type := loop n (Constr.Binder.type bind) sub in 
        let bind := Constr.Binder.make id type in
        mk_prod bind body
      | Prod bind body, 1 :: sub => 
        let body := loop (Int.add n 1) body sub in
        mk_prod bind body
      (* Application. *)
      | App func args, 0 :: sub => 
        let func := loop n func sub in
        mk_app func args
      | App func args, i :: sub => 
        let args := 
          Array.mapi 
            (fun j arg => if Int.equal (Int.sub i 1) j then loop n arg sub else arg)
            args 
        in
        mk_app func args
      (* Invalid path. *)
      | _ => Control.throw (InvalidSubpath c sub)
      end
    end
  in
  loop 0 c sub.

Local Ltac2 binder_map (f : constr -> constr) (b : binder) : binder :=
  Binder.unsafe_make (Binder.name b) (Binder.relevance b) (f (Binder.type b)).

Local Ltac2 map_invert (f : constr -> constr) (iv : case_invert) : case_invert :=
  match iv with
  | NoInvert => NoInvert
  | CaseInvert indices => CaseInvert (Array.map f indices)
  end.

(** [map_with_binders g f n c] maps [f] on the immediate subterms of [c]; it is
    not recursive and the order with which subterms are processed is
    not specified. It also carries a lift index [n] (typically an integer) 
    which is processed by [g] at each binder traversal. 
    
    This should be shipped with Ltac2 (maybe it will in a future release of Coq). *)
Ltac2 map_with_binders (lift : 'a -> binder -> 'a) (f : 'a -> constr -> constr) 
  (n : 'a) (c : constr) : constr :=
  match kind c with
  | Rel _ | Meta _ | Var _ | Sort _ | Constant _ _ | Ind _ _
  | Constructor _ _ | Uint63 _ | Float _ | String _ => c
  | Cast c k t =>
      let c := f n c
      with t := f n t in
      make (Cast c k t)
  | Prod b c =>
      let b := binder_map (f n) b
      with c := f (lift n b) c in
      make (Prod b c)
  | Lambda b c =>
      let b := binder_map (f n) b
      with c := f (lift n b) c in
      make (Lambda b c)
  | LetIn b t c =>
      let b := binder_map (f n) b
      with t := f n t
      with c := f (lift n b) c in
      make (LetIn b t c)
  | App c l =>
      let c := f n c
      with l := Array.map (f n) l in
      make (App c l)
  | Evar e l =>
      let l := Array.map (f n) l in
      make (Evar e l)
  | Case info x iv y bl =>
      let x := match x with (x,x') => (f n x, x') end
      with iv := map_invert (f n) iv
      with y := f n y
      with bl := Array.map (f n) bl in
      make (Case info x iv y bl)
  | Proj p r c =>
      let c := f n c in
      make (Proj p r c)
  | Fix structs which tl bl =>
      let tl := Array.map (binder_map (f n)) tl in
      let n_bl := Array.fold_left lift n tl in
      let bl := Array.map (f n_bl) bl in
      make (Fix structs which tl bl)
  | CoFix which tl bl =>
      let tl := Array.map (binder_map (f n)) tl in
      let n_bl := Array.fold_left lift n tl in
      let bl := Array.map (f n_bl) bl in
      make (CoFix which tl bl)
  | Array u t def ty =>
      let ty := f n ty
      with t := Array.map (f n) t
      with def := f n def in
      make (Array u t def ty)
  end.

(** [deep_pattern pat c sub] replaces occurences of [pat] which are in the subterm of [c] 
    at path [sub] by a local variable, and abstracts over this variable.
   
    For instance : 
      deep_pattern '(x + 1) '(P (x + 1) /\ P (x + 1)) [ 2 ]
    gives
      '(fun a => P (x + 1) /\ P a)
*)
Ltac2 deep_pattern (pat : constr) (c : constr) (sub : int list) : constr :=
  (* For some reason [Std.pattern] does not work on terms with loose de Bruijn indices. 
     We thus have to write our custom version of [pattern]. *)
  let rec replace (depth : int) (sc : constr) : constr :=
    if Constr.equal sc pat then mk_rel (Int.add 1 depth)
    else map_with_binders (fun depth _ => Int.add 1 depth) replace depth sc
  in
  (* Replace the pattern by a de Bruijn index. *)
  let body := map_subterm replace c sub in
  (* Add a binder. *)
  let bind := Constr.Binder.make (Some @x) (Constr.type pat) in
  mk_lambda bind body. 