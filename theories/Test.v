From Actema Require Import Loader.
From Actema Require Import DnD.

Lemma test : (2=2 /\ 3=3) -> 2=2 /\ 3=3.
Proof.
  intro H.
  calltac "back" H
    (cons false (@nil bool))
    (cons false (@nil bool))
    (cons true (cons false nil))
    empty_inst.
  calltac "back" H
    (cons true (@nil bool))
    (@nil bool)
    (cons false (@nil bool))
    empty_inst.
Qed.