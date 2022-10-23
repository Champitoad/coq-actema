From Actema Require Import Loader.

Lemma test A B : (A /\ B) -> A /\ B.
Proof.
  intro H.
  actema.
  actema "2steps".
Qed.

Require Import Lia.

Parameters A : Prop.

Lemma test_eq (n m : nat) : (A -> A) /\ 3 + 4 * 5 < 25.
  actema.
  lia.
Qed.

(* Lemma yolo (U : Set) (t u : U) (R : Prop) (P : U -> Prop) (f : U -> U -> U) :
  P(t) -> f t u = f u t -> t = u -> P(u) /\ R.
Proof.
  intros.
  actema.
Admitted. *)

Lemma peano_inj : forall x : nat, 0 = S x.
Proof.
  actema.
Admitted.

Lemma robinson_ind :
  forall x, x = 0 \/ exists y, x = S y.
Proof.
  actema.
Admitted.

Lemma fa_ex (A : Set) (P : nat -> Prop) (t : nat) :
  (forall y, P y) -> exists x, P x.
Proof.
  intros.
  actema; simpl.
  exists 0; auto.
Qed.

Lemma test_rew t u f :
  t = u -> S (S (f t t)) = f u u -> f (S t) 5 = 42.
Proof.
  intros. actema.
Admitted.

Lemma test_instantiate (n : nat) (P : nat -> Prop) (A : Prop) :
  (forall x, P x) \/ A -> A /\ exists x, P x.
Proof.
  intros. actema. admit.
Admitted.
  