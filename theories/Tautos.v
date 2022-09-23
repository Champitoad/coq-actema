From Actema Require Import Loader.

Context (A B C D E F G : Prop).

(** * Implication *)

Lemma id : A -> A.
Proof.
  actema; auto.
Qed.

Lemma K_combinator : A -> B -> A.
Proof.
  actema; auto.
Qed.

Lemma swap_args : (A -> B -> C) -> B -> A -> C.
Proof.
  actema; auto.
Qed.

Lemma compose : (A -> B) -> (B -> C) -> A -> C.
Proof.
  actema; auto.
Qed.

(** * Conjunction *)

Lemma and_comm : A /\ B -> B /\ A.
Proof.
  actema; auto.
Qed.

Lemma and_intro : A -> B -> A /\ B.
Proof.
  actema; auto.
Qed.

Lemma and_elim_l : A /\ B -> A.
Proof.
  actema; auto.
Qed.

Lemma and_elim_r : A /\ B -> B.
Proof.
  actema; auto.
Qed.

Lemma currying : (A /\ B -> C) -> A -> B -> C.
Proof.
  actema; auto.
Qed.

Lemma uncurrying : (A -> B -> C) -> (A /\ B -> C).
Proof.
  actema; auto.
Qed.

Lemma and_imp_weak_distr : (A -> B) /\ C -> A -> B /\ C.
Proof.
  actema; auto.
Qed.

Lemma and_assoc : A /\ (B /\ C) <-> (A /\ B) /\ C.
Proof.
  actema; auto.
Qed.

Lemma imp_and_distr : (A -> B /\ C) <-> (A -> B) /\ (A -> C).
Proof.
  actema; auto.
Qed.

Lemma jn_switch : (A /\ (B /\ (C /\ D -> E) -> F) -> G) -> A /\ D /\ (B /\ (C -> E) -> F) -> G.
Proof.
  actema; auto.
Qed.

Print jn_switch.

Lemma jn_switch_clicks : (A /\ (B /\ (C /\ D -> E) -> F) -> G) -> A /\ D /\ (B /\ (C -> E) -> F) -> G.
Proof.
  actema "clicks".
Qed.

Print jn_switch_clicks.

(** * Disjunction *)

Lemma switch : A /\ (B \/ C) -> (A /\ B) \/ C.
Proof.
  actema; auto.
Qed.

Lemma or_intro_l : A -> A \/ B.
Proof.
  actema; auto.
Qed.

Lemma or_intro_r : B -> A \/ B.
Proof.
  actema; auto.
Qed.

Lemma or_elim : A \/ B -> (A -> C) -> (B -> C) -> C.
Proof.
  actema; auto.
Qed.

Lemma imp_or_distr : (A -> B) \/ (A -> C) -> A -> B \/ C.
Proof.
  actema; auto.
Qed.

Lemma or_imp_weak_distr : (A -> B) \/ C -> A -> B \/ C.
Proof.
  actema; auto.
Qed.

Lemma or_assoc : A \/ (B \/ C) <-> (A \/ B) \/ C.
Proof.
  actema; auto.
Qed.

Lemma imp_or_anti_distr : (A \/ B -> C) <-> (A -> C) /\ (B -> C).
Proof.
  actema; auto.
Qed.

Lemma or_and_distr : A \/ B /\ C <-> (A \/ B) /\ (A \/ C).
Proof.
  actema; auto.
Qed.

(** * Negation *)

Lemma contra : A -> ~A -> B.
Proof.
  actema; auto.
Qed.

Lemma contra_disj : A -> (~A \/ B) -> B.
Proof.
  actema; auto.
Qed.

Lemma disj_contra : ~A -> (A \/ B) -> B.
Proof.
  actema; auto.
Qed.

Lemma not_not : A -> ~~A.
Proof.
  actema; auto.
Qed.

Lemma not_not_tnd : ~~(A \/ ~A).
Proof.
  actema; auto.
Qed.

Lemma double_neg_modus_ponens : ~~(A -> B) -> ~~A -> ~~B.
Proof.
  actema; auto.
Qed.

Lemma double_neg_imp : (~~A -> ~~B) -> ~~(A -> B).
Proof.
  (* BUG: some DnD proofs do not work out correctly *)
  actema; auto.
Qed.

Lemma demorgan_and : ~ A \/ ~ B -> ~ (A /\ B).
Proof.
  actema; auto.
Qed.

Lemma demorgan_or : ~ A /\ ~ B -> ~ (A \/ B).
Proof.
  actema; auto.
Qed.

(** * Truth *)

Lemma true_intro : True.
Proof.
  actema; auto.
Qed.

Lemma true_elim : A -> True -> A.
Proof.
  actema; auto.
Qed.

(** * Falsity *)

Lemma efq : False -> A.
Proof.
  actema; auto.
Qed.