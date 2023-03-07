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
  pose proof le_S.
  pose proof le_refl.
  actema.
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
  
Lemma plus_moins : forall n m p,
    n = m + p -> m = moins n p.
  pose proof eq_S.
  pose proof moinsnn.
  pose proof PeanoNat.Nat.add_0_r.
  pose proof PeanoNat.Nat.add_succ_r.
  pose proof add_comm.
actema.
Qed.

Lemma le_ex : forall n m, le m n -> exists p, n = m + p.
  actema.
Qed.


Lemma moins_plus : forall m n,
    n = moins (m + n) m.
 actema.
Qed.

Lemma plus_le : forall m p, le p (m+p).
  pose proof le_refl.
  pose proof le_S.
  actema.
Qed.

Lemma plus_eq_le : forall m n p, n = m + p -> le p n.
pose proof plus_le.  
actema.
Qed.

Lemma le_moins : forall m n, le m n -> n = (moins n m) + m.
  pose proof le_ex.
  pose proof plus_moins.
  pose proof add_comm.
  actema.
Qed.


Fixpoint even n :=
  match n with
  | 0 => True
  | S n => ~ (even n)
  end.

  
Lemma div_even :
  forall p, even (p+p).
  pose proof PeanoNat.Nat.add_succ_r.
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
  actema.
Qed.

Fixpoint double n :=
  match n with
  | 0 => 0
  | S m => S (S (double m))
  end.

Fixpoint div2 n :=
  match n with
  | S (S m) => S (div2 m)
  | _ => 0
  end.

Lemma nneven : forall n, ~~even n -> even n.
  actema.
Qed.

Lemma S_le : forall n m, le (S n) m -> le n m.
  actema.
Qed.


(* assez moche car des fix apparaissent *)
Lemma even_div2_aux : forall m, forall n, le n m -> even n -> n = double(div2 n).
pose proof S_le.
pose proof nneven.
actema.
Qed.

Lemma even_div2 : forall n, even n -> n = double(div2 n).
pose proof even_div2_aux.
pose proof le_refl.
actema.
Qed.
(* Un pb - vérifier mes instanciations *)
