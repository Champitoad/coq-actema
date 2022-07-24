From Actema Require Import Loader.

Parameters (A B C D E : Prop).

(** * Implication *)

Lemma id : A -> A.
Proof.
  actema.
Qed.

Lemma K_combinator : A -> B -> A.
Proof.
  actema.
Qed.

Lemma swap_args : (A -> B -> C) -> B -> A -> C.
Proof.
  actema.
Qed.

Lemma compose : (A -> B) -> (B -> C) -> A -> C.
Proof.
  actema.
Qed.

(** * Conjunction *)

Lemma and_comm : A /\ B -> B /\ A.
Proof.
  actema.
Qed.

Lemma and_intro : A -> B -> A /\ B.
Proof.
  actema.
Qed.

Lemma and_elim_l : A /\ B -> A.
Proof.
  actema.
Qed.

Lemma and_elim_r : A /\ B -> B.
Proof.
  actema.
Qed.

Lemma currying : (A /\ B -> C) -> A -> B -> C.
Proof.
  actema.
Qed.

Lemma uncurrying : (A -> B -> C) -> (A /\ B -> C).
Proof.
  actema.
Qed.

Lemma and_imp_weak_distr : (A -> B) /\ C -> A -> B /\ C.
Proof.
  actema.
Qed.

Lemma and_assoc : A /\ (B /\ C) <-> (A /\ B) /\ C.
Proof.
  actema.
Qed.

(** * Negation *)

Lemma demorgan_and : ~ A \/ ~ B -> ~ (A /\ B).
Proof.
  actema.
Qed.

Lemma demorgan_or : ~ A /\ ~ B -> ~ (A \/ B).
Proof.
  actema.
Qed.

(** * Truth *)

Lemma true_intro : True.
Proof.
  actema.
Qed.

Lemma true_elim : A -> True -> A.
Proof.
  actema.
Qed.

(** * Falsity *)

Lemma efq : False -> A.
Proof.
  actema.
Qed.