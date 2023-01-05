From Actema Require Import Loader.
Require Import ssreflect.

Parameter Rich : nat -> Prop.
Parameter mother : nat -> nat.
Parameter h : nat.

(* Definition imm0 : inst1.
exists 0.
intros; exact (mother (mother 0)).
Defined.
Definition im0 : inst1.
exists 0.
intros; exact (mother 0).
Defined. *)

Lemma eduk1 :
  (forall x : nat, ~Rich(x) -> Rich(mother(x))) ->
  (forall x : nat,  ~Rich(mother(mother(x))) \/ ~Rich(x))->
  False.
Proof.
  intros.
  Set Ltac Profiling.
  actema_force.
  Show Ltac Profile CutOff 1.
Qed.

Context (A B C D E F G : Prop).
Context (P Q : nat -> Prop) (R S : nat -> nat -> Prop) (t : nat).

Context (a b : nat).

Goal (B -> a = b) -> P b -> C.
intros h p. actema_force.
rew_dnd_hyp test
true

h

p

p0

(true :: nil)%list

(@nil bool)

(0 :: nil)%list

(true :: false :: nil)%list

(@nil (option (inst1 test))).

Lemma S_inj : forall n m, S n = S m -> n = m.
Admitted.

Lemma addS : forall n m, n + (S m) = S (n + m).
move => n.
induction n; simpl; trivial.
intros m; rewrite IHn; trivial.
Qed.

Definition icl1 : nat -> (list (option (inst1 test))).
intro n; apply cons; try apply nil.
apply Some; exists 0.
intros; exact n.
Defined.
Definition ic : nat -> (option (inst1 test)).
intro n; apply Some; exists 0.
intros; exact n.
Defined. 

Lemma ex_pred : forall x p, S(S x) = Nat.add p p ->
                            exists q, x = Nat.add q  q.
move => x [//=|p].
pose h := addS.
pose s_i := S_inj.
simpl.
intros.
actema.
(* A la place de divers "not found" *)
rew_dnd_hyp test h H hh
            (cons false (cons false ( nil)))
            (@nil bool)(cons 1 (cons 0 nil))
             (cons false (cons false (cons true nil)))
             (cons (ic p)(cons (ic p) nil)).
back test s_i
     (cons false (cons false (cons true nil)))
     (@nil bool)
     (cons false (cons false (cons false nil)))
     (cons (ic ( x)) (cons (ic ( (p+p))) nil)).
back test s_i
     (cons false (cons false (cons true nil)))
     (@nil bool)
     (cons false (cons false (cons false nil)))
     (cons (ic (S x)) (cons (ic (S (p+p))) nil)).

forward test s_i hh hhh
        (cons false (cons false (cons false nil)))
        (@nil bool)
        (cons false (cons false (cons false nil)))
        (cons (ic (S x)) (cons (ic (S (p+p))) nil)).
forward test s_i hhh hhhh
        (cons false (cons false (cons false nil)))
        (@nil bool)
        (cons false (cons false (cons false nil)))
        (cons (ic ( x)) (cons (ic ( (p+p))) nil)).
Abort.

Fixpoint le (n:nat)(m:nat) :=
  match n,m with
  | 0,_ => True
  | (S _) , 0  => False
  | S n, S m => le n m
  end.

Lemma ex_le : forall n m, (exists p, n = m + p)-> (le m n).
pose S_i := S_inj.
elim => [| n hn][|m]; actema_force.
Abort.