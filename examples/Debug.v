From Actema Require Import Loader.
Require Import ssreflect.

Lemma bug (P : nat -> Prop) h (h1 : forall x, P x) (h2 : P h -> False) : False.
Proof. actema_force. 

Lemma test2 (A B : Prop) (h : A -> B) : A -> B.
Proof. actema_force.

Parameter (Even : nat -> Prop).

Lemma example a (h : forall n, Even n -> Even (n + 2)) : 
  Even (a + 2).
Proof. 
  actema.