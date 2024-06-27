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

(* Here we can't rewrite the first 0 into f0 with <-[f 0 = 0]. *)
Parameter (f : nat -> nat).
Parameter (Q : nat -> Prop).
Lemma bug1 :
   Q 0 -> ~ (f 0) = 0.
actema_force.

(* Filter lemmas : only supports a single selection -> recover from this. *)

(* Double click on hypothesis : try discriminate. *)