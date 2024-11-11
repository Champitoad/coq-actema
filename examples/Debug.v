From Actema Require Import Loader.
Require Import ssreflect.

Lemma test2 (A B : Prop) (h : A -> B) : A -> B.
Proof. actema_force.

Parameter (Even : nat -> Prop).

Lemma example a (h : forall n, Even n -> Even (n + 2)) : 
  Even (a + 2).
Proof. 
  actema.