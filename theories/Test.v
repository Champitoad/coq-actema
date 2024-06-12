From Actema Require Import Loader.
Require Import ssreflect.


Lemma test : forall x, (fun _ : nat => True) x.
  actema_force.


Definition test : exists x : ((fun _ => nat) 42), 0 + x = 0 + 42.
  match goal with 
  | [ |- ?g ] => 
      let g' := simpl_path_r (cons 0 nil) g in
      change g'
  end.
