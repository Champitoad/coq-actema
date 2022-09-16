From Actema Require Import Loader.
From Actema Require Import DnD.

Lemma test A B : (A /\ B) -> A /\ B.
Proof.
  actema "2steps".
  actema "2steps".
Qed.

Definition k := 3.

Lemma test_eq (n m : nat) : 3 + 4 * 5 = 23.
  actema.
  easy.
Qed.