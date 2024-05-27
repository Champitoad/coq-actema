From Actema Require Import Loader.
Require Import ssreflect.

Lemma test : (4 + 0 = 55).
  set (f := fun n => 42 + n).
  actema_force.

Lemma test : True /\ False.
actema_force.

Lemma test (v : nat) : v = 0.
  let n : nat := 4 + 2.
actema_force. 

Inductive ll :=
  | lnil : ll
  | lcons : nat -> ll -> ll.

Inductive perm : ll -> ll -> Prop := 
  | perm_refl : forall l, perm l l.

