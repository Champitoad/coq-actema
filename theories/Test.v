From Actema Require Import Loader.

Lemma test (A B : Prop) : A -> (A -> B) -> B.
Proof.
  intros.
Abort.