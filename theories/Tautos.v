 From Actema Require Import Loader.

Require Import ssreflect.

Context (Socrates : bool).
Context (Mortal Human : bool -> Prop).

Parameter A B C D : Prop.
Lemma x1 : A -> A.
  intros H.
  Set Debug "backtrace".
actema.
Qed.

Check ltac:(let r := resize  (fun a b : nat => b) 0 2 0 1 in exact r).




Lemma Aristoteles (hm : forall x,  Human x -> Mortal x)
      (hh : Human Socrates):
  Mortal Socrates.
actema.
Qed.
(*
back hm (cons false (cons true nil))(@nil bool)
       (cons false (cons false nil))
       (cons (Some (mDYN _ (fun x:nat => Socrates))) nil)
  .
  exact hh.
(* 
actema_force. *)
Qed.
 *)

Parameter R : nat -> nat -> Prop.
Parameter a b : nat.

Lemma e1 (p:R a a) : exists x y: nat, R x y.

  pose ts := (tDYN nat :: nil)%list.

  Check ltac:(let r := reify_uncurry ts (nat -> nat -> nat)
                                     in exact r).
  back p (@nil bool)(cons false (cons false nil))
       (cons true (cons true nil))
       (cons (Some (mDYN _ (fun x  y: nat => a)))
             (cons (Some (mDYN _ (fun x  y: nat => a))) nil)).
Qed.
  
(*
  Ltac app_curry1 f a :=
  match a with
  | (?x1, ?c) =>
      let r := app_curry1 f c in
      constr:(r x1)
  | _ => constr:(f a)
  end.

  Ltac app_curry2 f a :=
  match a with
  | (?x1, ?c) =>  app_curry2 constr:(f x1) c 
  | _ => constr:(f a)
  end.
  
Check Nat.add.
  Check ltac:(let r :=
                app_curry1 (Nat.add) (3,4)
              in exact r).
  Check ltac:(let r :=
                app_curry2 (Nat.add) (3,4)
              in exact r).
  

  reify_goal ts (cons false (cons false nil)).
reify_hyp ts  (@nil bool) p .
pose g :=
   (ex (tDYN nat :: nil)%list nil 0 (fun x : nat => x)
       (ex (tDYN nat :: nil)%list (0 :: nil) 0 (fun y : nat => y)
          (Hole (tDYN nat :: nil)%list (0 :: 0 :: nil)
             (fun z : ppp (tDYN nat :: nil)%list (0 :: 0 :: nil) =>
              let (v0, rest0) := z in let (v1, _) := rest0 in R v1 v0)))).
pose hc :=
  (Hole (tDYN nat :: nil)%list nil (fun _ : ppp (tDYN nat :: nil)%list nil => R a b)).
pose t :=          (cons true (cons true nil)).
pose i1 :=   (cons (Some (mDYN _ (fun x y : nat => a)))
             (cons  (Some (mDYN _ (fun x y : nat => b))) 
                                                       nil)).
Eval compute in (bc3 ts 0 0 false t i1
                                nil
                                false nil hc nil g).
pose l :=   (cons
              (Some (mDYN (nat -> nat -> nat) (fun _ _ : nat => a), 0, 0))
              (cons (Some (mDYN (nat -> nat -> nat) (fun _ _ : nat => b), 0, 1))
                    nil)).
pose l2 := (cons (Some (mDYN (nat -> nat -> nat) (fun _ _ : nat => b), 0, 1))
                    nil).
pose l3 := ltac:(let r := dress ts l 0 2 in exact r).
apply (b3_corr  ts true t false l3 (@nil nat) tt (@nil nat) tt hc).
2 : simpl.
simpl.
rewrite /trl3 /= /eq_rect_r /eq_rect /eq_sym.


Check ltac:(let r := resize  (fun _ _ : nat => a) 0 2 0 0 in exact r).
Check ltac:(let r := dress1 ts a in exact r).
pose e1 := (insti ts 0 nil a).
Check ltac:(let r := resize  (fun _ _ : nat => b) 0 2 0 1 in exact r).
Check ltac:(let r := dress1 ts (fun _ : nat => b) in exact r).
pose e2 := (insti ts 0 (0 :: nil)%list (fun _ : nat => b)).
back p (@nil bool) (cons false (cons false nil))
       (cons true (cons true nil))
       (cons (Some (mDYN _ (fun x y : nat => b)))
             (cons  (Some (mDYN _ (fun x y : nat => a))) 
                                                       nil)).

  Qed. *)

Lemma e2   (hm : forall x,  Human x -> Mortal x)
      (hm' :  Human Socrates -> Mortal Socrates)
      (hh : Human Socrates):
  exists y, Mortal y.
  back hm
       (cons false (cons true nil))
       (cons false nil)
       (cons true (cons false (cons false nil)))
       (cons (None)
             (cons (Some (mDYN _ (fun x y : bool => y))) nil)).
actema.
Qed.


Lemma exfa_faex (R : nat -> nat -> Prop) :
  (exists x, forall y, R x y) -> (forall a, exists b, R b a).
Proof.
intro h.

back h (cons false (cons false nil))
     (cons false (cons false nil))
     (cons true (cons false (cons false (cons true nil))))
     (cons (Some (mDYN _ (fun x y a b : nat => a)))
           (cons  (Some (mDYN _ (fun x y a b : nat => y))) nil)).
                 
Qed.

Ltac depiot i :=
  match i with
  | cons _ (Some ?f) ?i' =>
      cut (refl_equal _ f);
      depiot i'
  | _ => idtac
  end.

depiot (cons (Some 4) nil).

generalize (refl_equal 3).

 back hm (cons false nil) (@nil bool)(cons false nil)
                        (cons (Some (mDYN _ Socrates)) nil)
                   .
                   
  

back_o (tDYN nat :: nil)%list hm (cons false nil)(@nil bool) (cons false nil)
         (cons (Some (mDYN _ ( Socrates))) nil).



Check ltac:(let r := dress1 (tDYN nat :: nil)%list (fun x:nat => Socrates) in exact r).


Check ltac:(let r := dress (tDYN nat :: nil)%list
                            (cons (Some (mDYN _ (fun x:nat => Socrates))) nil) in exact r).

pose ts :=  (tDYN nat :: nil)%list .
reify_goal ts (@nil bool).
reify_hyp ts (cons false nil) hm.



Check ltac:(let r := dress (tDYN nat :: nil)%list
                            (cons (Some (mDYN _ (fun x:nat => Socrates))) nil) in exact r).


apply (b3_corr ts false (cons false nil) false
               (Some
   (insti (tDYN nat :: nil) 0 (@nil nat) Socrates)
      :: nil)%list
               (@nil nat) tt (@nil nat) tt
                (fa (tDYN nat :: nil)%list nil 0 (fun x : nat => x)
            (Hole (tDYN nat :: nil)%list (0 :: nil)
               (fun z : ppp (tDYN nat :: nil)%list (0 :: nil) =>
                  let (v0, _) := z in Mortal v0)))
      );
  [idtac|assumption].
unfold b3.
unfold seq.cat.

apply trex_norm_apply.
simpl; try done; auto.




Check  ltac:(let r := mkSign (cons false nil) (forall x : nat, Mortal x) in exact r).

Check ltac:(let r := mkSignR (tDYN nat :: nil)%list (@nil bool) 

 (fun XX : (forall TT:Type, TT) => (Mortal Socrates)) in exact r).

Check ltac:(let r := dress1 (tDYN nat :: nil)%list (fun x:nat => Socrates) in exact r).





  actema.
                   back hm (cons false nil) (@nil bool)(cons false nil)
                        (cons (Some (mDYN _ (fun x:nat => x))) nil)
                   .
                   
  let tm := type of hm in let ts := mkSign  (cons false nil) tm in
                          reify_hyp ts (cons false nil) hm;
                          reify_goal ts (@nil bool).

  actema. b' hm (cons false nil)(@nil bool) (cons false nil) (@nil bool).
  actema_force.
Qed.

Parameter Rich : nat -> Prop.
Parameter mother : nat -> nat.
Parameter h : nat.

Lemma eduk1 :
  (forall x : nat, ~Rich(x) -> Rich(mother(x))) ->
  (forall x : nat,  ~Rich(mother(mother(x))) \/ ~Rich(x))->
  False.
Proof.
  intros.
  set john := h.
  actema.
Qed.

(* Algebra *)

Parameter f g : nat -> nat.
Lemma inv_d : (forall y, f (g y) = y) -> (forall x, exists y,  g y = x) ->
              forall x,  g (f x) = x.
actema.
Qed.

(** * Kaustuv's challenge *)

Context (A B C D E F G : Prop).
Context (P Q : nat -> Prop) (R S : nat -> nat -> Prop) (t : nat).
                                                          
Lemma kchal :
  (forall x y, R x y \/ R y x) ->
  (forall x y, S x y -> S y x -> x = y) ->
  (forall x y, R x y -> S x y) ->
  forall x y, S x y -> R x y.
Proof.
  intros.
  actema.
Qed.

Lemma ex_intro :
  P t -> exists x, P x.
Proof.
  intros.
  actema.
Qed.

Lemma ex_elim :
  (exists x, P x) -> (forall y, P y -> C) -> C.
Proof.
  intros.
  actema.
Qed. 

(** * Forall *)

Lemma fa_intro :
  (forall x, P x) -> (forall x, P x).
Proof.
  actema.
Qed.

Lemma fa_elim :
  (forall x, P x) -> P t.
Proof.
  intros.
  actema.
Qed.

(** * Exist/Forall *)

Lemma exfa_faex (R : nat -> nat -> Prop) :
  (exists x, forall y, R x y) -> (forall a, exists b, R b a).
Proof.
  actema.
Qed.

Lemma ex_demorgan :
  (forall x, ~ P x) -> ~ exists y, P y.
Proof.
  intros.
  actema.
  Restart.
  unfold not in *.
  intro.
  actema.
Qed.

Lemma bw :
  A -> (~ exists n : nat, A) -> False.
Proof.
  intros.
  actema.
Qed. 

(** * Implication *)

Lemma id : A -> A.
Proof.
  actema.
Qed.

Lemma K_combinator : A -> B -> A.
Proof.
  actema.
Qed.

Lemma swap_args : (A -> B -> C) -> B -> A -> C.
Proof.
  intros.
  actema.
Qed.

Lemma compose : (A -> B) -> (B -> C) -> A -> C.
Proof.
  actema.
Qed.

(** * Conjunction *)

Lemma and_comm : A /\ B -> B /\ A.
Proof.
  actema.
Qed.

Lemma and_intro : A -> B -> A /\ B.
Proof.
  actema.
Qed.

Lemma and_elim_l : A /\ B -> A.
Proof.
  actema.
Qed.

Lemma and_elim_r : A /\ B -> B.
Proof.
  actema.
Qed.

Lemma currying : (A /\ B -> C) -> A -> B -> C.
Proof.
  actema.
Qed.

Lemma uncurrying : (A -> B -> C) -> (A /\ B -> C).
Proof.
  actema.
Qed.

Lemma and_imp_weak_distr : (A -> B) /\ C -> A -> B /\ C.
Proof.
  actema.
Qed.

Lemma and_assoc : A /\ (B /\ C) <-> (A /\ B) /\ C.
Proof.
  actema.
Qed.

Lemma imp_and_distr : (A -> B /\ C) <-> (A -> B) /\ (A -> C).
Proof.
  actema.
Qed.

Lemma jn_switch : (A /\ (B /\ (C /\ D -> E) -> F) -> G) -> A /\ D /\ (B /\ (C -> E) -> F) -> G.
Proof.
  actema.
Qed.


Lemma jn_switch_clicks : (A /\ (B /\ (C /\ D -> E) -> F) -> G) -> A /\ D /\ (B /\ (C -> E) -> F) -> G.
Proof.
  actema "clicks".
Qed.


(** * Disjunction *)

Lemma switch : A /\ (B \/ C) -> (A /\ B) \/ C.
Proof.
  actema.
Qed.

Lemma or_intro_l : A -> A \/ B.
Proof.
  actema.
Qed.

Lemma or_intro_r : B -> A \/ B.
Proof.
  actema.
Qed.

Lemma or_elim : A \/ B -> (A -> C) -> (B -> C) -> C.
Proof.
  actema.
Qed.

Lemma imp_or_distr : ((A -> B) \/ (A -> C)) -> A -> B \/ C.
Proof.
  actema.
Qed.

Lemma or_imp_weak_distr : (A -> B) \/ C -> A -> B \/ C.
Proof.
  actema.
Qed.

Lemma or_assoc : A \/ (B \/ C) <-> (A \/ B) \/ C.
Proof.
  actema.
Qed.

Lemma imp_or_anti_distr : (A \/ B -> C) <-> (A -> C) /\ (B -> C).
Proof.
  actema.
Qed.

Lemma or_and_distr : A \/ B /\ C <-> (A \/ B) /\ (A \/ C).
Proof.
  actema.
Qed.


(** * Negation *)

Lemma contra : A -> ~A -> B.
Proof.
  actema.
Qed.

Lemma contra_disj : A -> (~A \/ B) -> B.
Proof.
  actema.
Qed.

Lemma disj_contra : ~A -> (A \/ B) -> B.
Proof.
  actema.
Qed.

Lemma not_not : A -> ~~A.
Proof.
  actema.
Qed.
     

Lemma not_not_tnd : ~~(A \/ ~A).
Proof.
  actema.
Qed.

Lemma double_neg_modus_ponens : ~~(A -> B) -> ~~A -> ~~B.
Proof.
  actema.
Qed.

Lemma double_neg_imp : (~~A -> ~~B) -> ~~(A -> B).
Proof.
  actema.
Qed.

Lemma demorgan_and : ~ A \/ ~ B -> ~ (A /\ B).
Proof.
  actema.
Qed.

Lemma demorgan_or : ~ A /\ ~ B -> ~ (A \/ B).
Proof.
  actema.
Qed.

(** * Truth *)

Lemma true_intro : True.
Proof.
  actema.
Qed.

Lemma true_elim : A -> True -> A.
Proof.
  actema.
Qed.

(** * Falsity *)

Lemma efq : False -> A.
Proof.
  actema.
Qed.
