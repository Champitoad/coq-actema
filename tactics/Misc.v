(* This file defines miscellaneous tactics that are called from Ocaml (see plugin/actions.ml). *)

From Ltac2 Require Import Ltac2 Printf.
From Actema Require Import Utils.

(* [rew_all_left hyp] where [hyp] has type [?a = ?b], rewrites [a] into [b] everywhere.
   If [a] is a variable we clear [hyp]. *)
Ltac2 rew_all_left (hname : ident) : unit := 
  let hyp := Control.hyp hname in 
  lazy_match! Constr.type hyp with 
  | ?a = ?b =>
    try (rewrite $hyp in *) ;
    if Constr.is_var a then Std.clear [ hname ] else ()
  | _ => ()
  end.

(* [rew_all_right hyp] where [hyp] has type [?a = ?b], rewrites [b] into [a] everywhere.
   If [b] is a variable we clear [hyp]. *)
Ltac2 rew_all_right (hname : ident) : unit := 
  let hyp := Control.hyp hname in 
  lazy_match! Constr.type hyp with 
  | ?a = ?b =>
    try (rewrite <- $hyp in *) ;
    if Constr.is_var b then Std.clear [ hname ] else ()
  | _ => ()
  end.

(* [mydestruct c] destructs [c]. If [c] is not a simple variable we 
   remember its old value using an equation. *)
Ltac2 mydestruct (c : constr) : unit := 
  if Constr.is_var c then 
    (* Simply destruct c. *)
    destruct $c
  else 
    (* Destruct c and remember its old value using a new equation. *)
    let eqn_id := Fresh.in_goal @E in
    generalize (refl_equal $c) ;
    destruct $c at -1 ;
    intro $eqn_id.

(* [myinduction c] performs induction on [c]. If [c] is not a simple variable we 
   remember its old value using an equation. *)
Ltac2 myinduction (c : constr) : unit := 
  if Constr.is_var c then 
    (* Simple indution on c. *)
    induction $c
  else 
    (* Induction on c and remember its old value using a new equation. *)
    let eqn_id := Fresh.in_goal @E in
    generalize (refl_equal $c) ;
    induction $c at -1 ;
    intro $eqn_id.

(* [deep_simpl c sub] call [simpl] on the subterm of [c] at path [sub]. *)
Ltac2 deep_simpl (c : constr) (sub : int list) : constr := 
  (* Take care that [Std.eval_simpl] does not work on terms with loose de Bruijn indices. *)
  let on_subterm n subterm :=
    (* Instantiate the loose indices. *)
    let evars := List.init n (fun _ => fresh_evar (Some @deep_simpl_0) None) in 
    let subterm := Constr.Unsafe.substnl (List.map mk_var evars) 0 subterm in
    (* Simplify. *)
    let subterm := Std.eval_simpl RedFlags.all None subterm in
    (* Abstract the evars. *)
    let subterm := Constr.Unsafe.closenl evars 1 subterm in 
    Std.clear evars ; subterm
  in
  map_subterm on_subterm c sub.

(* Thin wrapper around [deep_simpl] that acts on the conclusion. *)
Ltac2 deep_simpl_concl (sub : int list) : unit := 
  let new_concl := deep_simpl (Control.goal ()) sub in
  change $new_concl.

(* Thin wrapper around [deep_simpl] that acts on a given hypothesis. *)
Ltac2 deep_simpl_hyp (hname : ident) (sub : int list) : unit := 
  let new_hyp := deep_simpl (Constr.type (Control.hyp hname)) sub in
  change $new_hyp in $hname.

Lemma test (hhh : forall x, exists y, forall z, x + y = 0 + z) : True.
Proof. deep_simpl_hyp @hhh [1 ; 1 ; 1 ].
  
  