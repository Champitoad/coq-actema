From Actema Require Import Loader.

Parameter (A B C D E F : Prop).
Parameter (P Q : nat -> Prop) (R : nat -> nat -> Prop).

Section Intro.

Lemma socrates_mortal (i : Type) (Socrates : i) (Human Mortal : i -> Prop) :
  Human Socrates -> (forall x, Human x -> Mortal x) -> Mortal Socrates.
Proof.
  intros H1 H2. apply H2. exact H1.
Restart.
  intros.
  actema "backward". Undo.
  actema "forward".
Qed.

Print socrates_mortal.

Lemma identity :
  A -> A.
Proof.
  actema "demo".
Qed.

Print identity.

(** Disclaimer: some goals in the following won't be provable. This is to
    demonstrate the usefulness of Actema in *exploratory* settings, where the
    user lacks the information/intuition about provability, but still wants to
    perform some reasoning to sketch a possible (partial) proof. *)

Lemma dnd1 :
  C /\ B -> B /\ (C \/ A) /\ D.
Proof.
  intros H. split.
  * apply H.
  * split. left. apply H.
Restart.
  actema "demo".
Abort.

Lemma curry_dnd :
  ((A /\ B) -> C) -> (A -> B -> C) -> B -> C \/ D.
Proof.
  intros.
  actema "backward".
Restart.
  intros.
  Fail apply H.
  assert (H' : A /\ B \/ D -> C \/ D) by intuition. apply H'. clear H'.
Restart.
  intros.
  actema "forward".
Restart.
  intros.
  Fail apply H in H1.
  apply H0 in H1. left. assumption.
  Undo. Undo. Undo.
  assert (H0' : A -> C) by auto.
Abort.

Lemma inst_ex (x : nat) :
  P x -> exists y, P y.
Proof.
  intros.
  Fail apply H. Fail eapply H.
  exists x. apply H. Undo. Undo.
  eexists. eapply H.
Restart.
  intros.
  actema "unif". Undo.
  actema "manual".
Qed.

Lemma compositional_semantics (f g : nat -> nat) :
  (forall x, x <> 0 -> f x = g x) ->
  (exists y, P (f y) \/ Q y).
Proof.
  intros H.
  setoid_rewrite H.
  actema "demo".
  Show Proof.
Abort.


End Intro.

Section Advanced.

Lemma add_comm :
  forall n m, n + m = m + n.
Proof.
  pose proof PeanoNat.Nat.add_0_r.
  pose proof PeanoNat.Nat.add_succ_r.
  actema "demo".
Qed.

End Advanced.