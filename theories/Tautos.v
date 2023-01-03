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
  actema.
Qed.


Inductive ile (n:nat) : nat -> Prop :=
  | ilr :  ile n n
  | ils : forall m, ile n m -> ile n (S m).

Fixpoint leb (n:nat)(m:nat) :=
  match n,m with
  | 0,_ => true
  | (S _) , 0  => false
  | S n, S m => leb n m
  end.
 
Fixpoint le (n:nat)(m:nat) :=
  match n,m with
  | 0,_ => True
  | (S _) , 0  => False
  | S n, S m => le n m
  end.
  
Fixpoint gtb  (n:nat)(m:nat) :=
  match n,m with
  | 0,_ => false
  | (S _) , 0  => true
  | S n, S m => gtb n m
  end.

Lemma leb_gtb : forall n m, leb n m = negb (gtb n m).
actema.
Qed.

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


(* bug: simplify peut toujours fabriquer des termes
 avec des match / fix *)
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

Print ile.

Definition lee n m := ile n m.

Lemma ile_r : forall n m,  lee n m -> le n m.
  pose h1 := le_refl.
  pose h2 := le_S.
  actema.
Qed.

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

Definition  add n m := n + m.

Lemma plS x y : add (S x) y = S (add x y).
done.
Qed.

Definition ief : nat -> nat -> (option (inst1 test)).
intros n1 n2; apply Some; exists 0.
intros e1 e2.
exact (n1 + (e1 0 n2)).
Defined.

Lemma ex_le : forall n m, (exists p, n =  m + p)-> (le  m n).
pose S_i := S_inj.
pose h := PeanoNat.Nat.add_succ_r.
actema.
done.
Qed.

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

Definition icp (e : list DYN) : (sort e 1) -> (option (inst1 e)).
intros n; apply Some; exists 1.
intros; exact n.
Defined.

Lemma ex_pred : forall x p, S(S x) = p+p ->
                            exists q, x = q + q.
pose h := PeanoNat.Nat.add_succ_r.
pose s_i := S_inj.
actema.
actema.
Qed.

(*

Definition ee := (mDYN bool InitialRing.NotConstant
                    :: mDYN nat 0
                       :: mDYN unit abstract_key
                          :: mDYN BinNums.N BinNat.N.one
                             :: mDYN BinNums.Z BinIntDef.Z.one
                                :: mDYN Ascii.ascii Ascii.one
                                   :: mDYN String.string String.HelloWorld
                                      :: mDYN InitialRing.Nword InitialRing.NwI
                                      :: nil)%list.
simpl.


let h' := fresh "h" in
reify_eq_hyp
  ee
  h h'
    (cons false (cons false nil)).
reify_prop ee   (cons 1 nil)(cons false nil)
 .

 apply (b3_corr ee
         (cons false (cons false (cons true (cons true nil))))
                  (cons (icp ee ( p))(cons (icp ee p) nil))
     (@nil nat) tt (@nil nat) tt
 (fa ee nil 1
            (fa ee (1 :: nil) 1
               (equality ee (1 :: 1 :: nil) 1
                  (fun z : ppp ee (1 :: 1 :: nil) =>
                   let (v0, rest0) := z in let (v1, _) := rest0 in v1 + S v0)
                  (fun z : ppp ee (1 :: 1 :: nil) =>
                   let (v0, rest0) := z in let (v1, _) := rest0 in S (v1 + v0)))))
(impl ee nil
       (property ee nil 1 (fun z : ppp ee (1 :: nil) => let (v0, _) := z in S (S x) = v0)
          (fun _ : ppp ee nil => S (p + S p)))
       (fun _ : ppp ee nil => exists q : nat, x = q + q))).
2 : assumption.
apply trex_norm_apply ; [split; try reflexivity|idtac].           
rewrite /= !trs_corr.
Check trs_corr.


rewrite ?/ts /icp /coerce /b3 /trl3 /tr3 /o3_norm ?trs_corr /convert  /defs /appist ?trs_corr;
     rewrite  /coerce /b3 /trl3 /tr3 /o3_norm ?trs_corr /convert /cT /cB  /appist /sort /trad1 /nthc /list_rect /sort /sl;
   rewrite ?trs_corr /trs ?eqnqtdec_refl /eq_rect_r /eq_rect /Logic.eq_sym.
simplify_goal.

auto.
simpl in h'.

2 : simpl.
2 : rewrite /trl3 /= trs_corr.
2 : simpl.

rew_dnd
  ee
  h
  (cons false (cons false nil))
  (cons false nil)
  (cons 1 nil)
  (cons false (cons false (cons true (cons false nil))))
             (cons (icp ee p)(cons (icp ee p) nil)).

Qed. *)
(* encore un pb en backward ! *)

(*
(* A la place de divers "not found" *)
intro H.
simpl in H.
actema.
Definition ee := (mDYN bool InitialRing.NotConstant
                    :: mDYN nat 0
                       :: mDYN unit abstract_key
                          :: mDYN BinNums.N BinNat.N.one
                             :: mDYN BinNums.Z BinIntDef.Z.one
                                :: mDYN Ascii.ascii Ascii.one
                                   :: mDYN String.string String.HelloWorld
                                      :: mDYN InitialRing.Nword InitialRing.NwI
                                      :: nil)%list.
Eval compute in (sort ee 1).
                   
rew_dnd_hyp ee h
 H hh
            (cons false (cons false ( nil)))
            (@nil bool)(cons 1 (cons 0 nil))
             (cons false (cons false (cons true nil)))
             (cons (icp ee p)(cons (icp ee p) nil)).

rewrite /eq_ind_r /eq_ind /eq_sym in hh.

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
 

  
Inductive ln :=
  lnil
| lc : nat -> ln -> ln.

Fixpoint la l1 l2 :=
  match l1 with
  | lc x l => lc x (la l l2)
  | _ => l2
  end.

Goal forall l1 l2 l3,  (la l1 (la l2 l3)) = lnil.
actema.

Parameter f : nat -> nat -> nat.
Lemma test :(forall x:nat, forall y:nat, y=x).
intro y.
  actema.
  -> (forall x y, f x y = 0) -> forall x' y', 9 = f x' y' -> True.


  intros hf h1 x' y' h2.
 .actema.
Goal   forall x, x = lnil1.
actema_force.


Definition lel n l :=
  match l with
  | lnil => True
  | cons m _ => le n m
  end.

Fixpoint sorted l :=
  match l with
  | lnil => True
  | cons n l => (lel n l) /\ (sorted l)
  end.

Fixpoint napp l m :=
  match l with
  | lnil => m
  | cons x l => cons x (napp l m)
  end.

Lemma app_ass : forall l m n,
    napp (napp l m) n = napp l (napp m n).
  induction l.
  done.
  actema. *)

Lemma ex_aux :
  forall n, ((exists p, n = p + p) ->  even n)
/\ ((exists p, S n = p + p) ->  even (S n)).
pose h :=  PeanoNat.Nat.add_succ_r.
pose e_p := ex_pred.
actema.
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


(* algebra *)
Parameter f g : nat -> nat.
Lemma inv_d : (forall y, f (g y) = y) -> (forall x, exists y,  g y = x) ->
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
