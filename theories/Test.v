From Actema Require Import Loader.
Require Import ssreflect.


Parameter (P : nat -> Prop).
Lemma test a (b := a + a) : ~ forall x, exists y, P x /\ P y.
actema_force.



(* Here we can't rewrite the second 0 into f0 with <-[f 0 = 0]. *)
Parameter (f g : nat -> nat).
Lemma bug1 :
   ~f (g 0) = 0 -> ((f 0) = 0 -> False).
actema_force.

(* Simplify proof after dnds. *)

(* Simplify + try discriminate after case. *)

(* Remember equality after case/induction on closed subterm (not on quantifier). *)

(* Filter lemmas : only supports a single selection -> recover from this. *)