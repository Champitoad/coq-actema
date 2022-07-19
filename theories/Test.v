From Actema Require Import Loader.

Lemma test (A B : Prop) : A -> B -> A -> B -> A.
Proof.
  actema;
  actema;
  actema;
  actema;
  assumption.
Qed.