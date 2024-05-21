From Actema Require Import Loader.
Require Import ssreflect.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Lemma test : forall long_name, long_name = 2 + long_name * 3 \/ True.
actema_force.

Inductive ll :=
  | lnil : ll
  | lcons : nat -> ll -> ll.

Inductive perm : ll -> ll -> Prop := 
  | perm_refl : forall l, perm l l.

Instance perm_equiv : Equivalence perm. Admitted.
Instance lcons_proper : Proper (eq ==> perm ==> perm) lcons. Admitted.


Lemma Test : Proper (perm ==> perm) (fun x => lcons 3 x).
Proof. typeclasses eauto 10.



Lemma test : True.
test_tac.