From Actema Require Import Loader.
Require Import ssreflect.

fun A : Type => fun l : list A => _

Definition target (x : nat) {A : Type} (l : list A) {y : nat} : True := I.

Lemma test : True.
  test_tac.

Print mathcomp.ssreflect.eqtype.eqVneq
About app.

Fixpoint eqb n m :=
  match n, m with
  | 0, 0 => true
  | S n, S m => eqb n m
  | _, _ => false
  end.

Lemma test (a := 42) (h : exists x, forall y, x = y + 1) : True.
actema_force.


(* Searching lemmas twice in a row : "failed to apply new proof state". *)