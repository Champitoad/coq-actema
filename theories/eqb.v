From Actema Require Import Loader.
Require Import ssreflect.


(* We need at least a boolean test, having the propositional one allows more compact specifications *)

Fixpoint eqb n m :=
  match n, m with
  | 0, 0 => true
  | S n, S m => eqb n m
  | _, _ => false
  end.

Fixpoint eqr n m :=
  match n, m with
  | 0, 0 => True
  | S n, S m => eqr n m
  | _, _ => False
  end.

(* This is totally classic and works smoothly in Actema *)
 

Lemma eqb_eqr : forall n m, eqb n m = true -> eqr n m.
Admitted.


Lemma eqb_eq : forall n m, eqb n m = true -> n = m.
actema_force.
Qed.