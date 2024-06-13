From Actema Require Import Loader.
Require Import ssreflect.

Definition f := fun x => x + 1 = 3.

Lemma test (y := 42) : forall z, exists x : nat, f (x + (y + z)).
actema_force.


(* [get_subterm path term] gets the subterm at path [path] of the Coq term [term].
   [path] is a list of nat. 
   This fails if the subterm depends on a variable bound above it in [term]. *)
(*Ltac get_subterm_r path term :=
  match constr:(pair path term) with
  (* Base case. *)
  | (nil, _) => constr:(term)
  (* Lambda. *)
  | (cons 0 ?p', fun x : ?T => ?body) => get_subterm_r p' T
  | (cons 1 ?p', fun x : ?T => @?body x) => 
      lazymatch
        constr:(fun x : T =>
           ltac:(let body := beta1 body x in
                 let r := get_subterm_r p' body in exact r))
      with                    
      | (fun _ : _ => ?res) => res
      end
  (* Dependent product. *)
  | (cons 0 ?p', forall x : ?T, ?body) => get_subterm_r p' T
  | (cons 1 ?p', forall x : ?T, @?body x) => 
      lazymatch
        constr:(fun x : T =>
           ltac:(let body := beta1 body x in
                 let r := get_subterm_r p' body in exact r))
      with                    
      | (fun _ : _ => ?res) => res
      end
  (* Existential quantification. *)
  | (cons 0 ?p', exists x : ?T, ?body) => get_subterm_r p' T
  | (cons 1 ?p', exists x : ?T, @?body x) => 
      lazymatch
        constr:(fun x : T =>
           ltac:(let body := beta1 body x in
                 let r := get_subterm_r p' body in exact r))
      with                    
      | (fun _ : _ => ?res) => res
      end
  (* Application. *)
  | (cons 0 ?p', ?f ?x) => get_subterm_r p' f
  | (cons 1 ?p', ?f ?x) => get_subterm_r p' x
  end.
     
Ltac myinduction path :=
  match goal with
  | |- ?g =>
      let subterm := get_subterm_r path g in
      pose (the_subterm := subterm) ;
      induction subterm
  end.

Definition f := fun x => x + 1 = 3.

Lemma test y : exists x : nat, f (x + y).
  myinduction (cons 1 (cons 1 (cons 1 nil))).
*)