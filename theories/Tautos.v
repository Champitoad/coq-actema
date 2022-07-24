From Actema Require Import Loader.

Parameters (A B C D E : Prop).

Lemma id : A -> A.
Proof.
  actema.
Qed.

Lemma K_combinator : A -> B -> A.
Proof.
  actema.
Qed.