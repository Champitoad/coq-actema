(* This module contains utility functions for Ltac2. 
   It is used mainly by DnD.v *)

From Ltac2 Require Import Ltac2.

(* Smart constructor for [Constr.Unsafe.Rel]. *)
Ltac2 mk_rel (n : int) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Rel n).

(* Smart constructor for [Constr.Unsafe.Var]. *)
Ltac2 mk_var (id : ident) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Var id).

(* Smart constructor for [Constr.Unsafe.Evar]. *)
Ltac2 mk_evar (ev : evar) : constr := 
  Constr.Unsafe.make (Constr.Unsafe.Evar ev [| |]).
  
(* Smart constructor for [Constr.Unsafe.Lambda]. *)
Ltac2 mk_lambda (bind : binder) (body : constr) : constr := 
  Constr.Unsafe.make (Constr.Unsafe.Lambda bind body).

(* Smart constructor for [Constr.Unsafe.Prod]. *)
Ltac2 mk_prod (bind : binder) (body : constr) : constr := 
  Constr.Unsafe.make (Constr.Unsafe.Prod bind body).
  
(* Smart constructor for [Constr.Unsafe.App]. *)
Ltac2 mk_app (f : constr) (args : constr array) : constr := 
  Constr.Unsafe.make (Constr.Unsafe.App f args).

(* [binder_name c] returns the name of the binder of [c]. *)
Ltac2 binder_name (c : constr) : ident option := 
  match Constr.Unsafe.kind c with 
  | Constr.Unsafe.Lambda binder _ => Constr.Binder.name binder 
  | Constr.Unsafe.Prod binder _ => Constr.Binder.name binder 
  | _ => None
  end.

(* [beta_root c] forces the beta reduction at the root of [c], if [c] is a beta redex.
   Otherwise it returns [c] unchanged. *)
 Ltac2 beta_root (c : constr) : constr := 
  lazy_match! c with 
  | ?f ?x => 
    match Constr.Unsafe.kind f with 
    | Constr.Unsafe.Lambda _ body => Constr.Unsafe.substnl [ x ] 0 body
    | _ => c
    end
  | _ => c
  end.
  
(* [beta_equiv t1 t2] checks whether the terms [t1] and [t2] are beta equivalent. *)
Ltac2 beta_equiv (t1 : constr) (t2 : constr) : bool := 
  let t1 := Std.eval_cbv RedFlags.all t1 in 
  let t2 := Std.eval_cbv RedFlags.all t2 in 
  Constr.equal t1 t2.

(* [freh_evar basename type] creates a fresh evar with the type [type].
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
    | None => '(_ :> Type) 
    end
  in 
  (* We have to use a trick to ensure the evar has the right name. 
     We create an identity function with the correct type and binder name : 
     this binder name will magically get chosen as the evar name. *)
  let binder := Constr.Binder.make (Some id) type in
  let my_lambda := mk_lambda binder (mk_rel 1) in
  (* Create the evar. *)
  epose ($my_lambda _ :> $type) as $id ;
  hnf in $id ;
  id.
  
(* [abstract_ident ev c] replaces all occurences of the identifier [id] in [c]
   by a local (de Bruijn) variable, and binds this local variable with a lambda abstraction. 
   
   For instance : 
     [abstract_ident x (P x /\ A)] would give [fun x => P x /\ A]
     [abstract_ident y (P x /\ A)] would give [fun _ => P x /\ A]
*)
Ltac2 abstract_ident (id : ident) (c : constr) : constr :=
  (* First replace [id] by [Rel 0]. *)
  let body := Constr.Unsafe.closenl [ id ] 1 c in
  (* Create the binder. *)
  let type := Constr.type (mk_var id) in 
  let binder := Constr.Binder.make (Some id) type in
  (* Make the lambda abstraction. *)
  mk_lambda binder body.

(* [fun_to_forall f] returns a term beta-equivalent to [forall x, f x], 
   but when [f] is a lambda abstarction we take care to keep the binder name of [f] 
   and to beta reduce [f x]. *)
Ltac2 fun_to_forall (id : ident option) (f : constr) : constr :=   
  match Constr.Unsafe.kind f with 
  | Constr.Unsafe.Lambda binder body => 
    let binder := 
      match id with 
      | None => binder
      | Some id => Constr.Binder.make (Some id) (Constr.Binder.type binder) 
      end
    in
    mk_prod binder body
  | _ => '(forall x, $f x)
  end.

(* Exception raised when a subpath in a term is invalid. *)
Ltac2 Type exn ::= [ InvalidSubpath (constr, int list)].

(* [map_subterm f c sub] replaces the subterm [sc] of [c] at path [sub] with [f n sc],
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
      match Constr.Unsafe.kind c, sub with 
      (* Base case. *)
      | _, [] => f n c
      (* Lambda abstraction. *)
      | Constr.Unsafe.Lambda bind body, 0 :: sub => 
        let id := Constr.Binder.name bind in 
        let type := loop n (Constr.Binder.type bind) sub in 
        let bind := Constr.Binder.make id type in
        mk_lambda bind body
      | Constr.Unsafe.Lambda bind body, 1 :: sub => 
        let body := loop (Int.add n 1) body sub in
        mk_lambda bind body
      (* Product. *)
      | Constr.Unsafe.Prod bind body, 0 :: sub => 
        let id := Constr.Binder.name bind in 
        let type := loop n (Constr.Binder.type bind) sub in 
        let bind := Constr.Binder.make id type in
        mk_prod bind body
      | Constr.Unsafe.Prod bind body, 1 :: sub => 
        let body := loop (Int.add n 1) body sub in
        mk_prod bind body
      (* Application. *)
      | Constr.Unsafe.App func args, 0 :: sub => 
        let func := loop n func sub in
        mk_app func args
      | Constr.Unsafe.App func args, i :: sub => 
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

(* [deep_pattern pat c sub] replaces occurences of [pat] which are in the subterm of [c] 
   at path [sub] by a local variable, and abstracts over this variable.
   
   For instance : 
     deep_pattern '(x + 1) '(P (x + 1) /\ P (x + 1)) [ 2 ]
   gives
     '(fun a => P (x + 1) /\ P a)
*)
Ltac2 deep_pattern (pat : constr) (c : constr) (sub : int list) : constr :=
  (* Replace the pattern by a [Var] in the subterm. *)
  let on_subterm n sc :=
    (* We want to use Std.eval_pattern, but for some reason it messes up 
       when the terms contain loose de Bruijn indices (which is the case here). 
       To handle this we convert loose indices to evars, call Std.eval_pattern,
       and convert evars back to loose indices. *)
    (* Evars for the loose indices in [sc]. *)
    let evars := List.init n (fun _ => fresh_evar (Some @deep_pattern_0) None) in 
    (* Replace the loose indices by evars in [sc]. *)
    let sc_closed := Constr.Unsafe.substnl (List.map mk_var evars) 0 sc in
    (* Call the regular [pattern] tactic. *)
    lazy_match! Std.eval_pattern [ ( pat, Std.AllOccurrences ) ] sc_closed with 
    | ?f _ => 
      (* Evar for the argument of [f]. *)
      let ev_x := fresh_evar (Some @deep_pattern_) None in
      let ev_constr := mk_var ev_x in
      let app := beta_root '($f $ev_constr) in
      (* Replace the evars in [app] by loose indices. *)
      let app_closed := Constr.Unsafe.closenl (List.append evars [ ev_x ]) 1 app in
      (* Don't forget to clear the evars. *)
      Std.clear (ev_x :: evars) ;
      app_closed
    | _ => Control.throw Assertion_failure
    end
  in
  (* Replace the pattern by [Var 1] in the term. *)
  let body := map_subterm on_subterm c sub in
  (* Add a binder. *)
  let bind := Constr.Binder.make (Some @x) (Constr.type pat) in
  mk_lambda bind body. 
