From Actema Require Import Loader.

Lemma test (A B C : Prop) : A /\ B -> B /\ A.
Proof.
  actema.
Qed.