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
actema_force.
Admitted.

(* Here we can't rewrite the first 0 into f0 with <-[f 0 = 0]. *)
Parameter (f : nat -> nat).
Parameter (Q : nat -> Prop).
Lemma bug2 (h : Q 0) : ~ (1 = 0).
actema_force.

(* Double click on hypothesis : try discriminate. *)