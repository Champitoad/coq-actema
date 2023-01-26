Require Import stdpp.base.

From Actema Require Import Loader.

Parameter (A B C D E F : Prop).
Parameter (P Q : nat -> Prop) (R : nat -> nat -> Prop).

Section Intro.

Lemma socrates_mortal (i : Type) (Socrates : i) (Human Mortal : i -> Prop) :
  Human Socrates -> (∀ x, Human x -> Mortal x) -> Mortal Socrates.
Proof.
  intros H1 H2. apply H2. exact H1.
Restart.
  intros.
  actema_force "backward". Undo.
  actema_force "forward".
Qed.

Print socrates_mortal.

Lemma identity :
  A -> A.
Proof.
  actema_force "demo".
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
  actema_force "demo".
Abort.

Lemma curry_dnd :
  ((A /\ B) -> C) -> (A -> B -> C) -> B -> C \/ D.
Proof.
  intros.
  actema_force "backward".
Restart.
  intros.
  Fail apply H.
  assert (H' : A /\ B \/ D -> C \/ D) by intuition. apply H'. clear H'.
Restart.
  intros.
  actema_force "forward".
Restart.
  intros.
  Fail apply H in H1.
  apply H0 in H1. left. assumption.
  Undo. Undo. Undo.
  assert (H0' : A -> C) by auto.
Abort.

Lemma inst_ex (x : nat) :
  P x -> ∃ y, P y.
Proof.
  intros.
  Fail apply H. Fail eapply H.
  exists x. apply H. Undo. Undo.
  eexists. eapply H.
Restart.
  intros.
  actema_force "unif". Undo.
  actema_force "manual".
Qed.

(* Lemma apply_ex :
  (∀ x, P x -> Q x) -> ∃ y, Q y.
Proof.
  intros H.
  eexists. eapply H.
Restart.
  intros H.
  actema_force "demo".
Abort. *)

(* Lemma inst_cycles :
  (∃ y, ∀ x, R x y) <->
  (∀ x', ∃ y', R x' y').
Proof.
  split; intro; actema_force.
Abort. *)
(* 
Lemma toto :
  0 + 0 = 0.
Proof. 
  actema_force "demo".
Qed.

Lemma simple_rewrite (n m : nat) :
  n = m -> P n -> P m.
Proof.
  intros; actema_force "demo".
Qed.

Lemma rewrite_quantifier (f g : nat -> nat) :
  ∀ a, ∃ b, P (f a + g b).
Proof.
  pose proof PeanoNat.Nat.add_comm.
  Fail rewrite H.
  setoid_rewrite H.
  actema_force "demo".
Abort. *)

Lemma compositional_semantics (f g : nat -> nat) :
  (∀ x, x <> 0 -> f x = g x) ->
  (∃ y, P (f y) \/ Q y).
Proof.
  intros H.
  setoid_rewrite H. Show 2. Undo.
  actema_force "demo".
Abort.

End Intro.

Section Advanced.

Lemma add_comm :
  ∀ n m, n + m = m + n.
Proof.
  pose proof PeanoNat.Nat.add_0_r.
  pose proof PeanoNat.Nat.add_succ_r.
  actema "demo".
Qed.

End Advanced.