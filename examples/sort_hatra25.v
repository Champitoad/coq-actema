From Actema Require Import Loader.
Require Import ssreflect.
Require Import List.
Require Import Nat.

(** * A famous syllogism by Aristotle *)

Lemma Socrates_is_Mortal (i : Type) (Socrates : i) (Human : i -> Prop) (Mortal : i -> Prop) :
  Human Socrates /\ (forall x, Human x -> Mortal x) ->
  Mortal Socrates.
Proof.
  actema_force.
Qed.
Print Socrates_is_Mortal.

(** * Proving the correctness of insertion sort on lists of natural numbers *)

(** ** Definition of "sortedness" in Prop *)

Definition low n l :=
  match l with
  | nil => True
  | m :: _ => n <= m
  end.

Fixpoint sorted l :=
  match l with
  | nil => True
  | n :: l => low n l /\ sorted l
  end.

(** ** Definition of the insertion function *)

(* To allow Actema to display the code *)
Definition ifthl {A} (b:bool) (n1 : list A) n2 :=
  if b then n1 else n2.

Fixpoint insert n l :=
  match l with
  | nil => cons n nil
  | cons m l' =>
      ifthl (n <=? m)
        (cons n l)
        (cons m (insert n l'))
  end.

(** ** Insertion preserves sortedness *)

Lemma insert_sort : forall n l, sorted l ->
                                sorted (insert n l) /\
                                  forall m, le m n /\ low m l -> low m (insert n l).
                                  (* Arguably, this invariant is the hard part of the proof. *)
  actema_force.
  (* Case when [leb n a] = true *)
  * actema_force.
  (* Case when [leb n a] = false *)
  * actema.
Qed.

(** ** Definition and correctness of insertion sort *)

Fixpoint insertion_sort l :=
  match l with
  | nil => nil
  | cons n l => insert n (insertion_sort l)
  end.

Lemma sorted_insertion_sort : forall l,
    sorted (insertion_sort l).
  actema_force.
Qed.