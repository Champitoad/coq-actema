From Actema Require Import Loader.

(** * Peano arithmetic *)
 Definition icl1 : nat -> (list (option (inst1 test))).
intro n; apply cons; try apply nil.
apply Some; exists 0.
intros; exact n.
Defined.
Definition ic : nat -> (option (inst1 test)).
intro n; apply Some; exists 0.
intros; exact n.
Defined. 

Lemma add_comm :
  forall n m, n + m = m + n.
Proof.
  pose proof PeanoNat.Nat.add_0_r.
  pose proof PeanoNat.Nat.add_succ_r.
  actema. actema.
Qed.

Inductive ile (n:nat) : nat -> Prop :=
  | ilr :  ile n n
  | ils : forall m, ile n m -> ile n (S m).

Fixpoint le (n:nat)(m:nat) :=
  match n,m with
  | 0,_ => True
  | (S _) , 0  => False
  | S n, S m => le n m
  end.


Fixpoint moins n m :=
  match m,n with
  | 0,_ => n
  | S m, S n => moins n m
  | S _, 0 => 0
  end.

Require Import ssreflect.

Lemma le_ex : forall n m, le n m  ->
                          exists p, n+p = m.
actema.
Qed.  

Lemma le_refl : forall n, le n n.
 actema.
Qed.

Lemma le_0 : forall n, le 0 n.
actema.
Qed.

Lemma le_S : forall n m,
       le n m -> le n (S m).
actema.
Qed.



Fixpoint even n := match n with
                   | 0 => True
                   | S n => ~(even n)
                   end.

Fixpoint eqb n m :=
  match n, m with
  | 0, 0 => True
  | S n, S m => eqb n m
  | _, _ => False
  end.

Lemma eqb_eq : forall n m,
    eqb n m -> n = m.
actema.
Qed.


Lemma eqb_refl : forall n, eqb n n.
actema.
Qed.

Lemma eq_eqb : forall n m, n=m -> eqb n m.
pose h2 := eqb_refl.
actema.
Qed.

Lemma S_inj : forall n m, S n = S m -> n =m.
pose h1 := eqb_eq.
pose h2 := eq_eqb.    
actema.
Qed.


Definition lee n m := ile n m.

Lemma ile_r : forall n m,  lee n m -> le n m.
  pose h1 := le_refl.
  pose h2 := le_S.
  actema.
Qed.
Search lee.

Lemma lee0 : forall n, lee 0 n.
have h1 : (forall n : nat, lee n n) by constructor.
have h2 : (forall n m, lee n m -> lee n (S m))
  by constructor.
actema.
Qed.

Lemma leeSS : forall n m, lee n m -> lee (S n)(S m).
have h1 : (forall n : nat, lee n n) by constructor.
have h2 : (forall n m, lee n m -> lee n (S m))
  by constructor.
actema.
Qed.

Lemma rle_i : forall n m, le n m -> lee  n m.
have h1 : (forall n : nat, lee n n) by constructor.
have h2 : (forall n m, lee n m -> lee n (S m))
  by constructor.
pose h3 := lee0.
pose h4 := leeSS.

actema.
Qed.

Definition pl n m := n + m.

Lemma plS x y : pl (S x) y = S (pl x y).
done.
Qed.

Lemma ex_le : forall n m, (exists p, n = pl m p)-> (le  m n).
pose S_i := S_inj.
pose pls' := plS.
induction n; induction m; simpl; try done.
 by case.
actema.
Qed.
(* ca ne marche pas avec rew_dnd_hyp *)

  
Lemma even_aux :
  forall n, (even n) /\ (exists p, n = p + p)
            \/(~even n) /\  (exists p, n = S(p + p)).
pose h := PeanoNat.Nat.add_succ_r.
 actema.
Qed.


Lemma even_ex : forall n,  even n ->
                           (exists p, n = p + p).
pose h := even_aux.
actema.
Qed.


Lemma ex_pred : forall x p, S(S x) = p+p ->
                            exists q, x = q + q.
move => x [//=|p].
pose h := PeanoNat.Nat.add_succ_r.
pose s_i := S_inj.
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

done.
Qed.


Lemma ex_aux :
  forall n, ((exists p, n = p + p) ->  even n)
/\ ((exists p, S n = p + p) ->  even (S n)).
pose h :=  PeanoNat.Nat.add_succ_r.
pose e_p := ex_pred.
actema.
induction p.
done.
by rewrite h in H.

actema.
(* manque bouton 'done' *)
Qed.

Lemma ex_even :
  forall n, (exists p, n = p + p) -> even n.
pose h := ex_aux.
actema.
Qed.

Lemma le_minus :
  forall m n, le m n ->
              (moins n m) + m = n.
pose h :=  PeanoNat.Nat.add_succ_r.
  pose proof PeanoNat.Nat.add_0_r.
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
  actema.
Qed.

Require Import ssreflect.

Lemma ex_intro :
  P t -> exists x, P x.
Proof.
  intros.
  actema.
Qed.


(* bug export 
Lemma ex_elim :
  (exists x, P x) -> (forall y, P y -> C) -> C.
Proof.
  intros.
  actema_force.
Qed. *)

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

(* re-bug 
Lemma bw :
  A -> (~ exists n : nat, A) -> False.
Proof.
  intros.
  actema.
  by exists 0.
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

Print jn_switch.

Lemma jn_switch_clicks : (A /\ (B /\ (C /\ D -> E) -> F) -> G) -> A /\ D /\ (B /\ (C -> E) -> F) -> G.
Proof.
  actema "clicks".
Qed.

Print jn_switch_clicks.

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
Qed. *)


(* algebra *)
Parameter f g : nat -> nat.
Lemma inv_d : (forall y, f (g y) = y) -> (forall x, exists y,  x = g y) ->
              forall x,  g (f x) = x.
actema.
Qed.

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
  actema. 
Qed.

Definition icv : nat -> (option (inst1 test)).
intro n; apply Some; exists 0.
intros e1 e2; apply e2; exact n.
Defined.



Lemma div :
  forall n, exists p, (n = p+p \/ n = Datatypes.S(p+p)).
pose h :=  PeanoNat.Nat.add_succ_r.
actema.
Qed.



(*
Definition lmoins := locked moins.

Lemma debug: forall n m : nat,
 ( forall n m : nat, n + S m = S (n + m)) ->
                    moins n m + S m = S n.
  intros.
actema.
rew_dnd test H 
(cons false (cons false
                  nil))
 (cons 1 nil)(@nil bool)
 (cons false (cons false (cons false nil)))
  (cons (ic (lmoins n m))
                       (cons (ic m) nil))
.
 
  reify_prop test (cons 1 nil)(@nil bool).

  reify_eq_hyp test
               H h
               (cons false (cons false
                                 nil)).

  apply (b3_corr test
                 (cons false (cons false (cons false nil)))
                 (cons (ic (moins n m))
                       (cons (ic m) nil))



                   (@nil nat) tt (@nil nat) tt
    (fa test nil 0
           (fa test (0 :: nil) 0
              (equality test (0 :: 0 :: nil) 0
                 (fun z : ppp test (0 :: 0 :: nil) =>
                  let (v0, rest0) := z in let (v1, _) := rest0 in v1 + S v0)
                 (fun z : ppp test (0 :: 0 :: nil) =>
                  let (v0, rest0) := z in let (v1, _) := rest0 in S (v1 + v0)))))

     (property test nil 0
       (fun z : ppp test (0 :: nil) => let (v0, _) := z in v0 = S n)
       (fun _ : ppp test nil => moins n m + S m))).
2 : assumption.  
 clear h;  apply trex_norm_apply.
split; reflexivity.

 rewrite /test /ic /coerce /b3 /trl3 /tr3 /o3_norm ?trs_corr /convert  /defs /appist ?trs_corr;
     rewrite  /coerce /b3 /trl3 /tr3 /o3_norm ?trs_corr /convert /cT /cB  /appist /sort /trad1 /nthc /list_rect /sort /sl;
  rewrite ?trs_corr /trs ?eqnqtdec_refl /eq_rect_r /eq_rect /Logic.eq_sym; 
  simplify_goal;
  rewrite  /sort /sl. 


  rewrite /coerce /o3_norm /b3 /trl3 /tr3 /o3_norm ?trs_corr /convert  /defs /appist ?trs_corr.
simplify_goal.  actema.
 *)
