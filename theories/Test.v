From Actema Require Import Loader.
Require Import ssreflect.


Lemma test : exists x : nat, (fun _ _ _ => True) x x x.
  actema_force.


Definition test : exists x : ((fun _ => nat) 42), 0 + x = 0 + 42.
  match goal with 
  | [ |- ?g ] => 
      let g' := simpl_path_r (cons 0 nil) g in
      change g'
  end.
