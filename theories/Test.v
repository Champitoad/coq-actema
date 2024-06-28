From Actema Require Import Loader.
Require Import ssreflect.

Fixpoint eqb n m :=
  match n, m with
  | 0, 0 => true
  | S n, S m => eqb n m
  | _, _ => false
  end.

Lemma test (a := 42) (h : exists x, forall y, x = y + 1) : True.
actema_force.


(* Searching lemmas twice in a row : "failed to apply new proof state". *)