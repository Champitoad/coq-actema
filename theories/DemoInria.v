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

Lemma curry_dnd :
  ((A /\ B) -> C) -> (A -> B -> C) -> A -> B -> C \/ D.
Proof.
  intros.
  actema.
  actema.
Restart.
actema.
Qed.

Print curry_dnd.

Lemma inst_ex (x : nat) :
  P x -> ∃ y, P y.
Proof.
  intros.
  actema.
Qed.

Lemma apply_ex :
  (∀ x, P x -> Q x) -> ∃ y, Q y.
Proof.
  actema.
Qed.

