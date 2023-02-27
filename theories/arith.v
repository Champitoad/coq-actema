From Actema Require Import Loader.
Require Import ssreflect.


Lemma add_comm :
  forall n m, n + m = m + n.
Proof.
actema.
Qed.
     
Fixpoint eqb n m :=
  match n, m with
  | 0, 0 => true
  | S n, S m => eqb n m
  | _, _ => false
  end.

Fixpoint eqr n m :=
  match n, m with
  | 0, 0 => True
  | S n, S m => eqr n m
  | _, _ => False
  end.

    
Lemma eqr_eq : forall n m, eqr n m -> n = m.
  actema.
Qed.


Lemma eqr_eqb : forall n m, eqr n m -> eqb n m = true.
  actema.
Qed.

Lemma eqb_eqr : forall n m, eqb n m = true -> eqr n m.
  actema.
Qed.

Lemma eqr_refl : forall n, eqr n n.
actema.
Qed.

Lemma eq_eqr : forall n m, n=m -> eqr n m.
  pose proof eqr_refl.
  actema.
Qed.
(* deep ne marche pas car il manque une tactique *)

Lemma eqb_eq : forall n m, eqb n m = true -> n = m.
  actema.
Qed.

Lemma eqb_refl : forall n, eqb n n = true.
  actema.
Qed.
  
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



Lemma le_trans : forall a b c,
    le a b -> le b c -> le a c.
  actema.
Qed.

Lemma leb_le : forall n m, (leb n m = true) -> le n m.
  actema.
Qed.

Lemma le_refl : forall n, le n n.
  actema.
Qed.

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

Lemma le_S : forall n m,
       le n m -> le n (S m).
actema.
Qed.

Lemma le_nSn : forall n, le n (S n).
move => n; apply le_S; apply le_refl.
Qed.


Lemma leb_lt : forall n m, leb n m = false -> le m n.
  actema.
Qed.


Lemma leb_refl : forall n, leb n n = true.
  actema.
Qed.

Lemma div :
  forall n, exists p, (n = p+p \/ n = Datatypes.S(p+p)).
pose h :=  PeanoNat.Nat.add_succ_r.
actema.
Qed.


Lemma eq_S : forall n m, S n = S m -> n = m.
pose proof eqr_eq.
pose proof eq_eqr.
actema.
Qed.

Lemma moinsnn : forall n, moins n n = 0.
  actema.
Qed.

(*
Lemma debug : forall x y,(( x+y = y + x ) -> False)->False.
  pose proof add_comm.
actema.

  reify_prop
    (cons (mDYN nat 0) nil)
    (cons 0 nil)
             (cons false (cons false (cons false nil)))
 .
 reify_eq_hyp
       (cons (mDYN nat 0) nil)
       H
       H'
       (cons false (cons false nil)).

 
  actema.*)
  
  
Lemma plus_moins : forall n m p,
    n = m + p -> m = moins n p.
  pose proof eq_S.
  pose proof moinsnn.
  pose proof PeanoNat.Nat.add_0_r.
  pose proof PeanoNat.Nat.add_succ_r.
  pose proof add_comm.
actema.
Qed.
(* un rew fait dupliquer le but - ok a priori *)


Lemma le_ex : forall n m, le m n -> exists p, n = m + p.
  actema.
Qed.


Lemma moins_plus : forall m n,
    n = moins (m + n) m.
 actema.
Qed.

Lemma plus_le : forall m n p, n = m + p -> le p n.
  pose proof le_refl.
  pose proof le_S.
  pose proof eq_S.
  actema.
Qed.


Print ls.
Definition ic : nat -> option (inst1 (cons (tDYN nat) nil)).
intro n.
apply Some.
simpl.
exists 0; simpl.
intros; exact n.
Defined.

Lemma le_moins : forall m n, le m n -> n = (moins n m) + m.
  pose proof le_ex.
  pose proof plus_moins.
  pose proof add_comm.
  actema.
Qed.
(* regarder rew sous ex *)

Fixpoint even n :=
  match n with
  | 0 => True
  | S n => ~ (even n)
  end.

  
Lemma div_even :
  forall p, even (p+p).
  pose proof PeanoNat.Nat.add_succ_r.
  (* vérifier qu'est-ce qui se passe avec le rewrite quand on bouge le but *)
  actema.
Qed.

Lemma div_odd : 
  forall p, ~even (S (p+p)).
  pose proof PeanoNat.Nat.add_succ_r.
  pose proof div_even.
  actema.
Qed.

Lemma even_ex : forall n, even n ->
                          exists p, n = p+p.
  pose proof div.
  pose proof div_even.
  actema.
Qed.


Lemma odd_ex :forall n, ~even n ->
                          exists p, n = S(p+p).
  pose proof div.
  pose proof div_even.
  actema. actema.
(* bug côté interface : la trace est trop courte quand
on rewrite n=p+p dans ~(even n) en forward *)
Qed.

Goal (even 5) -> 4=5 -> even 7.
  intro h.

    rew_dnd_rev (cons (tDYN nat) nil) h
              (cons 0 nil)
              (@nil nat)
              (cons false nil)
              (cons true (cons true nil))
              (@nil (option (inst1 (cons (tDYN nat) nil)))).
                             
