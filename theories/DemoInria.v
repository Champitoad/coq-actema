Require Import stdpp.base.

From Actema Require Import Loader.

Parameter (A B C D E F : Prop).
Parameter (P Q : nat -> Prop).

Lemma socrates_mortal (Socrates : nat) (Human Mortal : nat -> Prop) :
  Human Socrates -> (∀ x, Human x -> Mortal x) -> Mortal Socrates.
Proof.
  intros.
  actema.
Qed.

Lemma identity :
  A -> A.
Proof.
  actema.
Qed.

Lemma dnd1 :
  C /\ B -> B /\ (C \/ A) /\ D.
Proof.
  actema.
Abort.