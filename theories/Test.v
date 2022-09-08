From Actema Require Import Loader.
From Actema Require Import DnD.

Lemma test A B : (A /\ B) -> A /\ B.
Proof.
  actema "2steps".
  actema "2steps".
Qed.