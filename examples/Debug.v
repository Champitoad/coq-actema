From Actema Require Import Loader.
Require Import ssreflect.

Lemma test (A B : Prop) (h : A -> B) : A -> B.
Admitted.

Lemma test2 (A : Prop) (h : A) (h' : not A) : False.
Proof. actema_force.

Parameter (Even : nat -> Prop).

Lemma example a (h : forall n, Even n -> Even (n + 2)) : 
  Even (a + 2).
Proof. 
  actema.