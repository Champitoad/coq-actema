From Actema Require Import Loader.
Require Import ssreflect.

Goal 3+4 = 7.
unfold_path (cons 1 nil).

Parameter P : nat -> Prop.
Lemma bug3 (e : 4 = 4) : exists x, P x.
actema.


Axiom triche : forall R : nat -> nat -> Prop, forall x : nat, forall y : nat, R x y.

Lemma l1 : forall x : nat, forall y : nat, P x y.
actema_force.
