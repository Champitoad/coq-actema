From Actema Require Import Loader.
Require Import ssreflect.

Lemma S_inj : forall n m, S n = S m -> n = m.
Admitted.

Fixpoint le (n:nat)(m:nat) :=
  match n,m with
  | 0,_ => True
  | (S _) , 0  => False
  | S n, S m => le n m
  end.

Lemma ex_le : forall n m, (exists p, n = m + p)-> (le m n).
pose S_i := S_inj.
elim => [| n hn][|m]; actema_force.
done.
Qed.