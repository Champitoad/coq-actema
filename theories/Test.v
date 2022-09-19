From Actema Require Import Loader.
From Actema Require Import DnD.

Lemma test A B : (A /\ B) -> A /\ B.
Proof.
  actema "2steps".
  actema "2steps".
Qed.

Require Import Lia.

Parameters A : Prop.

Lemma test_eq (n m : nat) : (A -> A) /\ 3 + 4 * 5 < 25.
  actema.
  lia.
Qed.

Lemma yolo (U : Set) (t u : U) (P : U -> Prop) (f : U -> U -> U) :
  P(t) -> f t u = f u t -> t = u -> P(u).
Proof.
  intros.
  actema.
Admitted.