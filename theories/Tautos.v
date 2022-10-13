From Actema Require Import Loader.

Context (A B C D E F G : Prop).
Context (P Q : nat -> Prop) (R S : nat -> nat -> Prop) (t : nat).

(** * Kaustuv's challenge *)

Lemma kchal :
  (forall x y, R x y \/ R y x) ->
  (forall x y, S x y -> S y x -> x = y) ->
  (forall x y, R x y -> S x y) ->
  forall x y, S x y -> R x y.
Proof.
  intros.
  actema.
  generalize H3; rewrite fw1; trivial.
Qed.

Require Import ssreflect.

(** * Existential *)
Definition gx : (pp (cons 0 nil)) -> nat.
  move => [x _].
  exact x.
Defined.

Definition itest : option inst1.
  apply Some; exists 0; move => e1 e2.
  apply e2; exact 0.
Defined.

Lemma test_inst :
  (forall x, x = t) -> exists x, P x.
Proof.
  intros.
  change (coerce (@nil nat)
    (fa _ 0
      (equality _ 0
        gx (fun _ => t))) tt) in H.
  change (coerce (@nil nat)
    (ex _ 0 
    (property _ 0
      (fun c => 
        P (let (x,_):=c in x))
        gx)) tt).

        apply 
        (b3_corr 
        (cons true (cons false (cons false nil))) 
        (cons None (cons itest nil))
      (@nil nat) 
      tt
      (@nil nat)
      tt
      (fa nil 0
      (equality (0 :: nil) 0 gx (fun _ : pp (0 :: nil) => t)))
      (ex nil 0
      (property (0 :: nil) 0
          (fun c : pp (0 :: 0 :: nil) => P (let (x, _) := c in x)) gx))
        ).

  simpl.
  rewrite /trl3 /=.

  cbn.
Abort.

Lemma ex_intro :
  P t -> exists x, P x.
Proof.
  intros.
  actema.
Qed.

Definition iin : (list (option inst1)).
  apply cons.
  apply Some.
  exists 0.
intros e1 e2.  
apply e1; exact 0.
  apply nil.
Defined.

Lemma ex_elim :
  (exists x, P x) -> (forall y, P y -> C) -> C.
Proof.
  intros.
  actema "forward".
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
(*
  forward
    H0
    H
    fw
    (false :: nil)%list
    (false :: false :: nil)%list
    (false :: true :: true :: nil)%list
    (Some (existT (fun s : nat => env -> env -> sort s) 0 (fun env1 _ : env => env1 0 0))
    :: nil)%list.*)

Lemma bw :
  A -> (~ exists n : nat, A) -> False.
Proof.
  intros.
  actema.
Admitted.

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
  (* BUG: some DnD proofs do not work out correctly *)
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
Admitted.

                                                  


                                                          
