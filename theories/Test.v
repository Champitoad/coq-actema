From Actema Require Import Loader.
Require Import ssreflect.

Lemma test : True /\ False.
actema_force.

Inductive ll :=
  | lnil : ll
  | lcons : nat -> ll -> ll.

Inductive perm : ll -> ll -> Prop := 
  | perm_refl : forall l, perm l l.

