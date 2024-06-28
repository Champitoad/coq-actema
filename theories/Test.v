From Actema Require Import Loader.
Require Import ssreflect.

Fixpoint eqb n m :=
  match n, m with
  | 0, 0 => true
  | S n, S m => eqb n m
  | _, _ => false
  end.

(* Here we can't instantiate [x]. *)
Parameter (P : nat -> Prop).
Lemma test a (b := a + a) : ~ forall x, exists y, P x /\ P y.
Admitted.

Parameter (Q : nat -> Prop).
Lemma bug2 (h : Q 0) : ~ (0 = 1).
rew_dnd_rev 
  h 
  (cons 1 nil) 
  (cons 1 nil) 
  (cons true (cons false nil)) 
  (@nil (option DYN)).


(* Searching lemmas twice in a row : "failed to apply new proof state". *)