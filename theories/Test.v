From Actema Require Import Loader.
Require Import ssreflect.

Parameter H : Prop.


Goal forall x : nat, x = 0.
Proof. actema_force. Admitted.


(* forall intro : fix the error. *)

Lemma test (v : nat) : v = 0.
  let n : nat := 4 + 2.
actema_force. 

Inductive ll :=
  | lnil : ll
  | lcons : nat -> ll -> ll.

Inductive perm : ll -> ll -> Prop := 
  | perm_refl : forall l, perm l l.

