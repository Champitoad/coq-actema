From Actema Require Import Loader.

Parameter (A B C D E F : Prop).
Parameter (P Q : nat -> Prop) (R : nat -> nat -> Prop).

Lemma socrates_mortal (i : Type) (Socrates : i) (Human Mortal : i -> Prop) :
  Human Socrates -> (forall x, Human x -> Mortal x) -> Mortal Socrates.
Proof.
  intros H1 H2. apply H2. exact H1.
Restart.
  intros.
  actema_force. Undo.
  actema_force.
Qed.

Print socrates_mortal.

Lemma dnd1 :
  C /\ B -> B /\ (C \/ A) /\ D.
Proof.
  intros H. split.
  * apply H.
  * split. left. apply H.
Restart.
  actema_force.
Abort.

Lemma curry_dnd :
  ((A /\ B) -> C) -> (A -> B -> C) -> B -> C \/ D.
Proof.
  actema_force.
Abort.

Lemma inst_ex (x : nat) :
  P x -> exists y, P y.
Proof.
  intros.
  actema_force.
Qed.

Lemma compositional_semantics (f g : nat -> nat) :
  (forall x, x <> 0 -> f x = g x) ->
  (exists y, P (f y) \/ Q y).
Proof.
  intros H.
  setoid_rewrite H. Undo.
  actema_force.
Abort.

Lemma add_comm :
  forall n m, n + m = m + n.
Proof.
  (* pose proof PeanoNat.Nat.add_0_r.
  pose proof PeanoNat.Nat.add_succ_r. *)
  actema_force. Undo.
  actema_force.
Qed.
