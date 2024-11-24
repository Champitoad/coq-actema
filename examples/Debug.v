From Actema Require Import Loader.
Require Import ssreflect.

Lemma bug (x y : nat) (h : x = y) : x = y.
actema_force.  
Qed.

Parameter test : nat -> nat -> bool.
Lemma bug2  (refl : forall n, test n n = true): 
 forall a, test a a = true.
 actema_force.
 intro.
 reflexivity.
 Unshelve.
Qed.

Parameter f g : nat -> nat.

Lemma bug (x y : nat) (h : x = y) (e : x = f y) : x = y.
actema_force.

Lemma test2 (A B : Prop) (h : A -> B) : A -> B.
Proof. actema_force.

Parameter (Even : nat -> Prop).

Lemma example a (h : forall n, Even n -> Even (n + 2)) : 
  Even (a + 2).
Proof. 
  actema.