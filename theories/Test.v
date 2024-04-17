From Actema Require Import Loader.
Require Import ssreflect.

Lemma test : True.
actema_force.


Parameter f : nat -> nat -> nat.

Inductive color := red | blue.
Inductive nlist (b : bool) : Set :=
  | ntriv : nlist b.

Lemma add_comm : prod (@eq bool false false) (false = false).
Proof. Admitted.

Lemma t2 (f : nat -> Set) : True.
  test_tac.
Admitted.

Check list. 

Lemma t1 (x : nlist false) : True.
  test_tac.

Lemma t (H : nduo false 42 42 = nduo false 42 42) : True.
  test_tac.

Context (P : color -> Prop).
Context (x y : color).

Lemma essai :
P red -> (forall x, x=red ) -> P blue.
intros h1 h2.
actema.
test.
(* pose xxx:= blue. *)

actema_force.
Qed.

Parameter (A B C : Prop) (P : nat -> Prop).

Parameter f : nat -> nat -> nat.
Lemma test : (forall x y, f x y = 0) ->
forall x y, 99 = f x y -> True.
intros h1 x y h2.
actema.
Abort.

Lemma tetest  (n:nat)(e:n+n=n+n) : exists p, n+n = p.
  Set Debug "backtrace".
  actema.
Abort.

Goal forall n m,
(exists p, m = n+p) ->
(exists p, n+p = m).
intros n m [p H].
actema.
Abort.

Lemma test A B : (A /\ B) -> A /\ B.
Proof.
  intro H. actema.
Qed.

Require Import Lia.

Lemma test_eq (n m : nat) : 2 + 4 = 6 -> (A -> A) /\ 5 + 4 * 5 = 25.
  actema.
Qed.

(* Lemma yolo (U : Set) (t u : U) (R : Prop) (P : U -> Prop) (f : U -> U -> U) :
  P(t) -> f t u = f u t -> t = u -> P(u) /\ R.
Proof.
  intros.
  actema.
Admitted. *)

Lemma peano_inj : forall x : nat, 0 = S x.
Proof.
  actema.
Admitted.

Lemma robinson_ind :
  forall x, x = 0 \/ exists y, x = S y.
Proof.
  actema.
Admitted.

Lemma fa_ex (A : Set) (P : nat -> Prop) (t : nat) :
  (forall y, P y) -> exists x, P x.
Proof.
  intros.
  actema.
Qed.

Lemma test_rew t u f :
  t = u -> S (S (f t t)) = f u u -> f (S t) 5 = 42.
Proof.
  intros.
  actema.
Admitted.

Lemma test_instantiate (n : nat) (P : nat -> Prop) (A : Prop) :
  (forall x, P x) \/ A -> A /\ exists x, P x.
Proof.
  intros.
  actema.
Admitted.
  