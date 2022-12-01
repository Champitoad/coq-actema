From Actema Require Import Loader.

(** * Peano arithmetic *)
Definition icl1 : nat -> (list (option inst1)).
intro n; apply cons; try apply nil.
apply Some; exists 0.
intros; exact n.
Defined.
Definition ic : nat -> (option inst1).
intro n; apply Some; exists 0.
intros; exact n.
Defined.

Lemma add_comm :
  forall n m, n + m = m + n.
Proof.
  pose proof PeanoNat.Nat.add_0_r.
  pose proof PeanoNat.Nat.add_succ_r.
  induction n; induction m; actema.
Qed.

(** * Kaustuv's challenge *)

Context (A B C D E F G : Prop).
Context (P Q : nat -> Prop) (R S : nat -> nat -> Prop) (t : nat).

Lemma kchal :
  (forall x y, R x y \/ R y x) ->
  (forall x y, S x y -> S y x -> x = y) ->
  (forall x y, R x y -> S x y) ->
  forall x y, S x y -> R x y.
Proof.
  actema.
Qed.

Require Import ssreflect.

Lemma ex_intro :
  P t -> exists x, P x.
Proof.
  intros.
  actema.
Qed.

Lemma ex_elim :
  (exists x, P x) -> (forall y, P y -> C) -> C.
Proof.
  intros.
  actema.
Qed.

(** * Forall *)

Lemma fa_intro :
  (forall x, P x) -> (forall x, P x).
Proof.
  actema.
Qed.

Lemma fa_elim :
  (forall x, P x) -> P t.
Proof.
  intros.
  actema.
Qed.

(** * Exist/Forall *)

Lemma exfa_faex (R : nat -> nat -> Prop) :
  (exists x, forall y, R x y) -> (forall a, exists b, R b a).
Proof.
  actema.
Qed.

Lemma ex_demorgan :
  (forall x, ~ P x) -> ~ exists y, P y.
Proof.
  intros.
  actema.
  Restart.
  unfold not in *.
  intro.
  actema.
Qed.

Lemma bw :
  A -> (~ exists n : nat, A) -> False.
Proof.
  intros.
  actema.
  by exists 0.
Qed.

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
  intros.
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

Lemma imp_and_distr : (A -> B /\ C) <-> (A -> B) /\ (A -> C).
Proof.
  actema.
Qed.

Lemma jn_switch : (A /\ (B /\ (C /\ D -> E) -> F) -> G) -> A /\ D /\ (B /\ (C -> E) -> F) -> G.
Proof.
  actema.
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
  actema.
Qed.

Lemma or_intro_l : A -> A \/ B.
Proof.
  actema.
Qed.

Lemma or_intro_r : B -> A \/ B.
Proof.
  actema.
Qed.

Lemma or_elim : A \/ B -> (A -> C) -> (B -> C) -> C.
Proof.
  actema.
Qed.

Lemma imp_or_distr : ((A -> B) \/ (A -> C)) -> A -> B \/ C.
Proof.
  actema.
Qed.

Lemma or_imp_weak_distr : (A -> B) \/ C -> A -> B \/ C.
Proof.
  actema.
Qed.

Lemma or_assoc : A \/ (B \/ C) <-> (A \/ B) \/ C.
Proof.
  actema.
Qed.

Lemma imp_or_anti_distr : (A \/ B -> C) <-> (A -> C) /\ (B -> C).
Proof.
  actema.
Qed.

Lemma or_and_distr : A \/ B /\ C <-> (A \/ B) /\ (A \/ C).
Proof.
  actema.
Qed.

(** * Negation *)

Lemma contra : A -> ~A -> B.
Proof.
  actema.
Qed.

Lemma contra_disj : A -> (~A \/ B) -> B.
Proof.
  actema.
Qed.

Lemma disj_contra : ~A -> (A \/ B) -> B.
Proof.
  actema.
Qed.

Lemma not_not : A -> ~~A.
Proof.
  actema.
Qed.

Lemma not_not_tnd : ~~(A \/ ~A).
Proof.
  actema.
Qed.

Lemma double_neg_modus_ponens : ~~(A -> B) -> ~~A -> ~~B.
Proof.
  actema.
Qed.

Lemma double_neg_imp : (~~A -> ~~B) -> ~~(A -> B).
Proof.
  actema.
Qed.

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

Parameter Rich : nat -> Prop.
Parameter mother : nat -> nat.
Parameter h : nat.

Definition imm0 : inst1.
exists 0.
intros; exact (mother (mother 0)).
Defined.
Definition im0 : inst1.
exists 0.
intros; exact (mother 0).
Defined.

(* algebra *)
Parameter f g : nat -> nat.
Lemma inv_d : (forall y, f (g y) = y) -> (forall x, exists y,  x = g y) ->
              forall x,  g (f x) = x.
actema.
Qed.
  
Lemma eduk1 :
  (forall x : nat, ~Rich(x) -> Rich(mother(x))) ->
  (forall x : nat,  ~Rich(mother(mother(x))) \/ ~Rich(x))->
  False.
Proof.
 intros h1 h2.
case (h2 0) => [h3|h3].
        forward h1 h3 h4
                (cons false (cons false nil))
                      (@nil bool)
                      (cons false (cons false nil))
                      (cons (Some imm0) nil).
                                                  forward h4 h2 h5
                                                          (@nil bool)
                                                          (cons false (cons false (cons false nil)))
                                                          (cons true (cons true (cons true nil)))
                      (cons (Some im0) nil).
forward h1 h5 h6 (cons false (cons false(nil)))(@nil bool)(cons false (cons false (nil)))                      (cons (Some im0) nil).
elim (h3 h6).  
Restart.
  (* Fail actema "bug_recheck_failure". *)
Admitted.
