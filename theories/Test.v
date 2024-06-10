From Actema Require Import Loader.
Require Import ssreflect.


Lemma test : forall x, forall y, x = y + 1.
test_tac.

(*Require Import mathcomp.ssreflect.seq.
Lemma test : 
  forall (T : eqtype.Equality.type) (x : eqtype.Equality.sort T),
  is_true (eqtype.eq_op x x).
Proof. test_tac.*)

Parameter (A : Prop) (B : Prop).

Lemma test (h : forall x, x = 0 \/ x = 3) : forall y, y = 3.
Proof. actema_force. 


Lemma test (v : nat) : v = 0.
  let n : nat := 4 + 2.
actema_force. 

Inductive ll :=
  | lnil : ll
  | lcons : nat -> ll -> ll.

Inductive perm : ll -> ll -> Prop := 
  | perm_refl : forall l, perm l l.

