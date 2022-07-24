From Actema Require Import Loader.

Lemma test (A B C : Prop) : A /\ (A -> B) /\ C /\ A -> B.
Proof.
  actema.
Qed.