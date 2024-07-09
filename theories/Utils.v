From Ltac2 Require Import Ltac2 Printf.

(* [beta_equiv t1 t2] checks whether the terms [t1] and [t2] are beta equivalent. *)
Ltac2 beta_equiv (t1 : constr) (t2 : constr) : bool := 
  let t1 := Std.eval_cbv RedFlags.all t1 in 
  let t2 := Std.eval_cbv RedFlags.all t2 in 
  Constr.equal t1 t2.

(* Create a fresh evar, optionally with a given type.
   Returns the evar as a constr. 
   
   TODO : figure out a way to actually name the evar. *)
Ltac2 fresh_evar (id : ident) (type_opt : constr option) : evar := 
  (* Create the evar as a constr. *)
  let t := 
    match type_opt with 
    | Some type => '(_ : $type)
    | None => '_
    end
  in 
  (* Extract the evar from the constr. *)
  match Constr.Unsafe.kind t with 
  | Constr.Unsafe.Evar ev _ => ev 
  | _ => Control.throw Assertion_failure
  end.

(* [is_evar ev t] checks if [t] is the evar [ev]. *)
Ltac2 is_evar (ev : evar) (t : constr) : bool :=
  match Constr.Unsafe.kind t with 
  | Constr.Unsafe.Evar ev' _ => Evar.equal ev ev'
  | _ => false 
  end.


Module MapWithBinders.
From Ltac2 Require Import Constr.

Local Ltac2 binder_map (f : constr -> constr) (b : binder) : binder :=
  Binder.unsafe_make (Binder.name b) (Binder.relevance b) (f (Binder.type b)).


Ltac2 main g f n c :=
  match Unsafe.kind c with  
  | Unsafe.Rel _ | Unsafe.Meta _ | Unsafe.Var _ | Unsafe.Sort _ 
  | Unsafe.Constant _ _ | Unsafe.Ind _ _ | Unsafe.Constructor _ _ 
  | Unsafe.Uint63 _ | Unsafe.Float _ => c
  | Unsafe.Cast c k t =>
      let c := f n c
      with t := f n t in
      Unsafe.make (Unsafe.Cast c k t)
  | Unsafe.Prod b c =>
      let b := binder_map (f n) b
      with c := f (g n) c in
      make (Prod b c)
  | Lambda b c =>
      let b := binder_map f b
      with c := f (g n) c in
      make (Lambda b c)
  | LetIn b t c =>
      let b := binder_map f b
      with t := f t
      with c := f c in
      make (LetIn b t c)
  | App c l =>
      let c := f c
      with l := Array.map (f n) l in
      make (App c l)
  | Evar e l =>
      let l := Array.map (f n) l in
      make (Evar e l)
  | Case info x iv y bl =>
      let x := match x with (x, x') => (f n x, x') end
      with iv := map_invert f iv
      with y := f n y
      with bl := Array.map (f n) bl in
      make (Case info x iv y bl)
  | Proj p r c =>
      let c := f n c in
      make (Proj p r c)
  | Fix structs which tl bl =>
      let tl := Array.map (binder_map f) tl
      with bl := Array.map f bl in
      make (Fix structs which tl bl)
  | CoFix which tl bl =>
      let tl := Array.map (binder_map f) tl
      with bl := Array.map f bl in
      make (CoFix which tl bl)
  | Array u t def ty =>
      let ty := f ty
      with t := Array.map f t
      with def := f def in
      make (Array u t def ty)
  end.


(* [map_with_binders g f n c] maps [f n] on the immediate
   subterms of [c]; it carries an extra data [n] (typically a lift
   index) which is processed by [g] (which typically add 1 to [n]) at
   each binder traversal; it is not recursive and the order with which
   subterms are processed is not specified.

   See also : Constr.map, Constr.iter_with_binders.
*)
Ltac2 map_with_binder 
  (g : 'a -> 'a) 
  (f : 'a -> constr -> constr) 
  (n : 'a) 
  (c : constr) 
  : constr 
:= MapWithBinders.main.

Ltac2 rec subst_evar (ev : evar) (n : int) (t : constr) : constr := 
  if is_evar ev t then 
    Constr.Unsafe.make (Constr.Unsafe.Rel n)
  else 
    map_with_binder 
      (fun n _ => Int.add 1 n) 
      (fun n child => subst_evar ev n child)
      n
      t.

(* [abstract_evar ev t] replaces all occurences of the evar [ev] in [t]
   by a local variable, and binds this local variable with a lambda abstraction. 
   
   For instance : 
     [abstract_evar ?x (P ?x /\ A)] would give [fun x => P x /\ A]
     [abstract_evar ?y (P ?x /\ A)] would give [fun _ => P ?x /\ A]
*)
Ltac2 abstract_evar (ev : evar) (t : constr) : constr :=
  (* First replace [ev] by [Rel 0]. *)
  let body := subst_evar ev 0 t in
  (* Create the binder. *)
  let id := Fresh.in_goal @x in
  let type := Constr.type (Constr.Unsafe.make (Constr.Unsafe.Evar ev [| |])) in 
  let binder := Constr.Binder.make (Some id) type in
  (* Make the lambda abstraction. *)
  Constr.Unsafe.make (Constr.Unsafe.Lambda binder body).
