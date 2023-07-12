From Actema Require Import Loader.

Section Edukera.

Context (Rich : nat -> Prop).
Context (mother : nat -> nat).
Context (h : nat).

Theorem rich_mothers :
  (forall x : nat, ~Rich(x) -> Rich(mother(x))) ->
  (forall x : nat,  ~Rich(mother(mother(x))) \/ ~Rich(x))->
  False.
Proof.
  actema.
Restart.
  intros H1 H2.
  destruct (H2 h) as [H | H].
  * pose proof (H1 _ H) as H'.
    (* If one naively uses `apply ... in`, then one loses H although it is
       needed later! Hence the use of `pose proof`. *)
    destruct (H2 (mother h)) as [H2' | H2'].
    - apply H2'. exact H'.
    - apply H1 in H2'.
      apply H. exact H2'.
  * pose proof (H1 _ H) as H'.
    destruct (H2 (mother h)) as [H2' | H2'].
    pose proof (H1 _ H2') as H2''.
    destruct (H2 (mother (mother h))) as [H2''' | H2'''].
    - apply H2'''. exact H2''.
    - pose proof (H1 (mother (mother h)) H2''') as H1'.
      apply H2'. exact H1'.
    - apply H2'. exact H'.
Qed.
    

End Edukera.

Section SetsAndFunctions.

Definition Ens {A : Type} := A -> Prop.

Definition incl {A : Type} (C D : Ens) :=
  forall (x : A), C x -> D x.

Definition im {A B : Type} (f : A -> B) (C : Ens) : Ens :=
  fun y => exists x, C x /\ y = f x.

Definition pre {A B : Type} (f : A -> B) (D : Ens) : Ens :=
  fun x => D (f x).

Definition injective {A B : Type} (f : A -> B) :=
  forall x x', f x = f x' -> x = x'.

Definition surjective {A B : Type} (f : A -> B) :=
  forall y, exists x, f x = y.

Definition inverse {A B : Type} (f : A -> B) (g : B -> A) :=
  forall a, g (f a) = a.

End SetsAndFunctions.

Section Surjective.

Theorem surjective_inverse {A B : Type} (f : A -> B) (g : B -> A) : 
  inverse f g -> surjective f -> inverse g f.  
Proof.
  unfold inverse, surjective.
  intros H1 H2 b.
  (* Tactic failure when trying to specialize H2 with b through DnD *)
Restart.
  unfold inverse, surjective.
  intros H1 H2 y.
  specialize (H2 y).
  destruct H2 as [x H2].
  rewrite <- H2.
  rewrite H1.
  reflexivity.
Admitted.

End Surjective.

Section Images.

Theorem subset_preimage_image {A B : Type} (f : A -> B) :
  forall C, incl C (pre f (im f C)).
Proof.
  unfold incl, pre, im.
  intros C x H.
  exists x.
  split.
  * exact H.
  * reflexivity.
Restart.
  unfold incl, pre, im.
  actema.
  (* Fail to translate, probably because of Ens... *)
Admitted.

Theorem preimage_image_subset {A B : Type} (f : A -> B) :
  injective f -> forall C, incl (pre f (im f C)) C.
Proof.
  unfold injective, incl, pre, im.
  intros H1 C x [a [Ha H2]].
  rewrite (H1 x a).
  * exact Ha.
  * exact H2.
Qed.

End Images.

Section Arith.

Theorem add_comm :
  forall (n m : nat), n + m = m + n.
Proof.
  actema.
  (* Graphical actions are in 1-to-1 correspondance with tactic invokations in
     this case, which makes the example not that interesting. One might say that
     this is a strength of the paradigm: this allows a smooth transition from
     graphical/textual styles, and would make Actema a good tool to teach proofs
     in imperative style without the burdens of hypothesis naming and learning
     the syntax of tactics. One could even imagine a tighter integration with
     the text editor, where graphical actions insert the corresponding tactic
     invokation in real time. But we still need to figure out the appropiate
     textual syntax for logical DnD actions. *)
Restart.
  induction n as [|n IHn].
  * induction m as [|m IHm].
    - reflexivity.
    - simpl.
      rewrite <- IHm.
      reflexivity.
  * induction m as [|m IHm].
    - simpl.
      rewrite IHn.
      reflexivity.
    - simpl.
      rewrite <- IHm.
      rewrite IHn.
      simpl.
      rewrite IHn.
      reflexivity.
Qed.

End Arith.