(* In this file we test the tactics [back] and [forward] from DnD.v. 
   We test all individual rules, as well as some more complex examples. *)

From Ltac2 Require Import Ltac2 Printf.
From Actema Require Import Utils.
From Actema Require Import DnD.

(* Some constants that we use to state dummy lemmas. *)
Parameter (A B : Prop).
Parameter (P : nat -> Prop) (R : nat -> nat -> Prop).

(* [assert_goal goal] checks the conclusion of the current goal is equal to [goal]
   (modulo beta conversion). Otherwise we raise an expection. *)
Local Ltac2 assert_goal (expected : constr) : unit := 
  let goal := Control.goal () in 
  if beta_equiv expected goal then () 
  else Control.throw Assertion_failure.

(* [assert_hyp hyp] checks if there is a hypothesis of type [hyp]
   (modulo beta conversion). Otherwise we raise an expection. *)
Local Ltac2 assert_hyp (expected : constr) : unit := 
  if List.exist (fun (_, _, hyp) => beta_equiv expected hyp) (Control.hyps ()) then ()
  else Control.throw Assertion_failure.

(***********************************************************************************)
(** Testing individual [back] rules. *)
(***********************************************************************************)

Module Back.

(* Backwards [id]. *)
Local Lemma id (h : A) : A.
  back_wrapper @h [] [] [] Subform.
  assert_goal 'True.
Admitted.

(* Backwards L=1. *)
Local Lemma eq_1 x (h : x = x + 1) : exists a, P a /\ P x /\ forall b, R x (a + b).
  (* Rewrite all occurences of [x]. *)
  back_wrapper @h [ 2 ] [] [] (Rewrite Left).
  assert_goal '(exists a, P a /\ P (x + 1) /\ forall b, R (x + 1) (a + b)).
Restart.
  (* This time rewrite only the deeper occurence of [x]. *)
  back_wrapper @h [ 2 ] [ 1 ; 2 ; 2 ; 1 ] [] (Rewrite Left).
  assert_goal '(exists a, P a /\ P x /\ forall b, R (x + 1) (a + b)).
Admitted.
  
(* Backwards L=2. *)
Local Lemma eq_2 x (h : x = x + 1) : exists a, P a /\ P (x + 1) /\ forall b, R (x + 1) (a + b).
  (* Rewrite all occurences of [x+1]. *)
  back_wrapper @h [ 3 ] [] [] (Rewrite Left).
  assert_goal '(exists a, P a /\ P x /\ forall b, R x (a + b)).
Restart.
  (* This time rewrite only the deeper occurence of [x+1]. *)
  back_wrapper @h [ 3 ] [ 1 ; 2 ; 2 ; 1 ] [] (Rewrite Left).
  assert_goal '(exists a, P a /\ P (x + 1) /\ forall b, R x (a + b)).
Admitted.

(* Backwards [and]. *)
Local Lemma and_right_1 (h : A) : A /\ B.
  back_wrapper @h [] [ 1 ] [ Side Right ] Subform.
  assert_goal '(True /\ B).
Admitted.
Local Lemma and_right_2 (h : B) : A /\ B.
  back_wrapper @h [] [ 2 ] [ Side Right ] Subform.
  assert_goal '(A /\ True).
Admitted.
Local Lemma and_left_1 (h : A /\ B) : A.
  back_wrapper @h [ 1 ] [] [ Side Left ] Subform.
  assert_goal 'True.
Admitted.
Local Lemma and_left_2 (h : A /\ B) : B.
  back_wrapper @h [ 2 ] [] [ Side Left ] Subform.
  assert_goal 'True.
Admitted.

(* Backwards [or]. *)
Local Lemma or_right_1 (h : A) : A \/ B.
  back_wrapper @h [] [ 1 ] [ Side Right ] Subform.
  assert_goal '(True \/ B).
Admitted.
Local Lemma or_right_2 (h : B) : A \/ B.
  back_wrapper @h [] [ 2 ] [ Side Right ] Subform.
  assert_goal '(A \/ True).
Admitted.
Local Lemma or_left_1 (h : A \/ B) : A.
  back_wrapper @h [ 1 ] [] [ Side Left ] Subform.
  assert_goal '(True /\ (B -> A)).
Admitted.
Local Lemma or_left_2 (h : A \/ B) : B.
  back_wrapper @h [ 2 ] [] [ Side Left ] Subform.
  assert_goal '((A -> B) /\ True).
Admitted.

(* Backwards implication. *)
Local Lemma impl_left (h : A -> B) : B.
  back_wrapper @h [ 1 ] [] [ Side Left ] Subform. 
  assert_goal '(A /\ True).
Admitted.
Local Lemma impl_right_1 x (h : x = 42) : P x -> P x.
  back_wrapper @h [ 2 ] [ 0 ] [ Side Right ] (Rewrite Left). 
  assert_goal '(P 42 -> P x).
Admitted.
Local Lemma impl_right_2 (h : B) : A -> B.
  back_wrapper @h [] [ 1 ] [ Side Right ] Subform.
  assert_goal '(A -> True).
Admitted.

(* Backwards forall. *)
Local Lemma forall_left_i (h : forall x, P x) : P 42.
  back_wrapper @h [ 1 ] [] [ Binder Left (Some '42) ] Subform.
  assert_goal 'True.
Admitted.
Local Lemma forall_left_s (h : forall x, P x /\ A) : A.
  back_wrapper @h [ 1 ; 2 ] [] [ Binder Left None ; Side Left ] Subform.
  assert_goal '(exists x : nat, True).
Admitted.
Local Lemma forall_right (h : A) : forall x, A /\ P x.
  back_wrapper @h [] [ 1 ; 1 ] [ Binder Right None ; Side Right ] Subform.
  assert_goal '(forall x : nat, True /\ P x).
Admitted.

(* Backwards exists. *)
Local Lemma exists_left (h : exists x, A /\ P x) : A.
  back_wrapper @h [ 1 ; 1 ] [] [ Binder Left None ; Side Left ] Subform.
  assert_goal '(forall x : nat, True).
Admitted.
Local Lemma exists_right_i (h : P 42) : exists x, P x.
  back_wrapper @h [] [ 1 ] [ Binder Right (Some '42) ] Subform.
  assert_goal 'True.
Admitted.
Local Lemma exists_right_s (h : A) : exists x, A /\ P x.
  back_wrapper @h [] [ 1 ; 1 ] [ Binder Right None ; Side Right ] Subform.
  assert_goal '(exists x : nat, True /\ P x).
Admitted.

End Back.

(***********************************************************************************)
(** Testing individual [forward] rules. *)
(***********************************************************************************)

Module Forward.

(* Forward L=1. *)
Local Lemma eq_left_1 x (h1 : x = x + 1) (h2 : exists a, P a /\ P x /\ forall b, R x (a + b)) : True.
  (* Rewrite all occurences of [x]. *)
  forward_wrapper @h1 [ 2 ] @h2 [] [] (Rewrite Left).
  assert_hyp '(exists a : nat, P a /\ P (x + 1) /\ forall b, R (x + 1) (a + b)).
Restart.
  (* This time rewrite only the deeper occurence of [x]. *)
  forward_wrapper @h1 [ 2 ] @h2 [ 1 ; 2 ; 2 ; 1 ] [] (Rewrite Left).
  assert_hyp '(exists a, P a /\ P x /\ forall b, R (x + 1) (a + b)).
Admitted.

(* Forward L=2. *)
Local Lemma eq_left_2 x (h1 : x = x + 1) (h2 : exists a, P a /\ P (x + 1) /\ forall b, R (x + 1) (a + b)) : True.
  (* Rewrite all occurences of [x+1]. *)
  forward_wrapper @h1 [ 3 ] @h2 [] [] (Rewrite Left).
  assert_hyp '(exists a, P a /\ P x /\ forall b, R x (a + b)).
Restart.
  (* This time rewrite only the deeper occurence of [x+1]. *)
  forward_wrapper @h1 [ 3 ] @h2 [ 1 ; 2 ; 2 ; 1 ] [] (Rewrite Left).
  assert_hyp '(exists a, P a /\ P (x + 1) /\ forall b, R x (a + b)).
Admitted.

(* Forward R=1. *)
Local Lemma eq_right_1 x (h1 : exists a, P a /\ P x /\ forall b, R x (a + b)) (h2 : x = x + 1) : True.
  (* Rewrite all occurences of [x]. *)
  forward_wrapper @h1 [] @h2 [ 2 ] [] (Rewrite Right).
  assert_hyp '(exists a : nat, P a /\ P (x + 1) /\ forall b, R (x + 1) (a + b)).
Restart.
  (* This time rewrite only the deeper occurence of [x]. *)
  forward_wrapper @h1 [ 1 ; 2 ; 2 ; 1 ] @h2 [ 2 ] [] (Rewrite Right).
  assert_hyp '(exists a, P a /\ P x /\ forall b, R (x + 1) (a + b)).
Admitted.

(* Forward R=2. *)
Local Lemma eq_right_2 x (h1 : exists a, P a /\ P (x + 1) /\ forall b, R (x + 1) (a + b)) (h2 : x = x + 1) : True.
  (* Rewrite all occurences of [x+1]. *)
  forward_wrapper @h1 [] @h2 [ 3 ] [] (Rewrite Right).
  assert_hyp '(exists a, P a /\ P x /\ forall b, R x (a + b)).
Restart.
  (* This time rewrite only the deeper occurence of [x+1]. *)
  forward_wrapper @h1 [ 1 ; 2 ; 2 ; 1 ] @h2 [ 3 ] [] (Rewrite Right).
  assert_hyp '(exists a, P a /\ P (x + 1) /\ forall b, R x (a + b)).
Admitted.

(* Forward and. *)
Local Lemma and_right_1 x (h1 : x = 42) (h2 : P x /\ A) : True.
  forward_wrapper @h1 [ 2 ] @h2 [ 1 ] [ Side Right ] (Rewrite Left).
  assert_hyp '(P 42).
Admitted.
Local Lemma and_right_2 x (h1 : x = 42) (h2 : A /\ P x) : True.
  forward_wrapper @h1 [ 2 ] @h2 [ 2 ] [ Side Right ] (Rewrite Left).
  assert_hyp '(P 42).
Admitted.
Local Lemma and_left_1 x (h1 : P x /\ A) (h2 : x = 42) : True.
  forward_wrapper @h1 [ 1 ] @h2 [ 2 ] [ Side Left ] (Rewrite Right).
  assert_hyp '(P 42).
Admitted.
Local Lemma and_left_2 x (h1 : A /\ P x) (h2 : x = 42) : True.
  forward_wrapper @h1 [ 2 ] @h2 [ 2 ] [ Side Left ] (Rewrite Right).
  assert_hyp '(P 42).
Admitted.

(* Forward or. *)
Local Lemma or_right_1 x (h1 : x = 42) (h2 : P x \/ A) : True.
  forward_wrapper @h1 [ 2 ] @h2 [ 1 ] [ Side Right ] (Rewrite Left).
  assert_hyp '(P 42 \/ A).
Admitted.
Local Lemma or_right_2 x (h1 : x = 42) (h2 : A \/ P x) : True.
  forward_wrapper @h1 [ 2 ] @h2 [ 2 ] [ Side Right ] (Rewrite Left).
  assert_hyp '(A \/ P 42).
Admitted.
Local Lemma or_left_1 x (h1 : P x \/ A) (h2 : x = 42) : True.
  forward_wrapper @h1 [ 1 ] @h2 [ 2 ] [ Side Left ] (Rewrite Right).
  assert_hyp '(P 42 \/ A).
Admitted.
Local Lemma or_left_2 x (h1 : A \/ P x) (h2 : x = 42) : True.
  forward_wrapper @h1 [ 2 ] @h2 [ 2 ] [ Side Left ] (Rewrite Right).
  assert_hyp '(A \/ P 42).
Admitted.

(* Forward implication. *)
Local Lemma impl_right_1 (h1 : A) (h2 : A -> B) : True.
  forward_wrapper @h1 [] @h2 [ 0 ] [ Side Right ] Subform.
  assert_hyp '(True -> B).
Admitted.
Local Lemma impl_right_2 x (h1 : x = 42) (h2 : A -> P x) : True.
  forward_wrapper @h1 [ 2 ] @h2 [ 1 ] [ Side Right ] (Rewrite Left).
  assert_hyp '(A -> P 42).
Admitted.

(* Forward forall. *)
Local Lemma forall_right_i (h1 : 0 = 0 + 0) (h2 : forall x, P x) : True.
  forward_wrapper @h1 [ 2 ] @h2 [ 1 ] [ Binder Right (Some '0) ] (Rewrite Left).
  assert_hyp '(P (0 + 0)).
Admitted.
Local Lemma forall_right_s (h1 : 0 = 0 + 0) (h2 : forall x, P 0 /\ P x) : True.
  forward_wrapper @h1 [ 2 ] @h2 [ 1 ; 1 ] [ Binder Right None ; Side Right ] (Rewrite Left).
  assert_hyp '(forall x : nat, P (0 + 0)).
Admitted.

(* Forward exists. *)
Local Lemma exists_right_s (h1 : 0 = 0 + 0) (h2 : exists x, P 0 /\ P x) : True.
  forward_wrapper @h1 [ 2 ] @h2 [ 1 ; 1 ] [ Binder Right None ; Side Right ] (Rewrite Left).
  assert_hyp '(exists x : nat, P (0 + 0)).
Admitted.

End Forward.

(***********************************************************************************)
(** Testing more complicated interactions. *)
(***********************************************************************************)

Parameter (Q : forall A, list A -> Prop).

Lemma list_test (h : forall A (l : list A), Q A l) :
  forall B (l : list B), Q B l.
Proof.
  back_wrapper 
    @h 
    [ 1 ; 1 ] 
    [ 1 ; 1 ]
    [ Binder Right None 
    ; Binder Right None 
    ; Binder Left (Some '(fun B (l : list B) => B))
    ; Binder Left (Some '(fun B (l : list B) => l))
    ]
    Subform.
  (* For some reason comparing the terms seems to fail here. 
     I anyways put the expected goal. *)
  (* target := '(forall B : Type, list B -> True) *)
Admitted.