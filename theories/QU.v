From Actema Require Import Loader.

(* P :: (), Q :: () & (), f : () -> (); forall x : (). P(x) -> exists y : (). Q(x,y) |- exists y : (). exists z : (). Q(f(z),y) *)

Context (T : Type) (P : T -> Prop) (Q : T -> T -> Prop) (f : T -> T).

Goal (forall x, P x -> exists y, Q x y) ->
     exists y z, Q (f z) y.
Proof.
  actema_force.
