From Actema Require Import Loader.
Require Import ssreflect.

Parameter (Even : nat -> Prop).

Lemma example a (h1 : Even a) (h2 : forall n, Even n -> Even (n + 2)) : 
  Even (a + 2).
Proof. 
  actema_force.
Admitted.















Lemma add_comm :
  forall n m, n + m = m + n.
Proof.
  actema_force.
  Unshelve. all: eauto.
Qed.
