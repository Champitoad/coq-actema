From Actema Require Import Loader.
Require Import ssreflect.

Lemma test (A : Prop) (h1 : A) (h2 : A -> B) (h3 : A) : True \/ False.
actema_force.
Admitted.

Lemma test2 (A : Prop) (h : A) (h' : not A) : False.
Proof. actema_force.

Parameter (Even : nat -> Prop).

Lemma example a (h : forall n, Even n -> Even (n + 2)) : 
  Even (a + 2).
Proof. 
  actema.