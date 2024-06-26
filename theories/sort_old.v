From Actema Require Import Loader.


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

Require Import ssreflect.
        
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

Lemma eqb_eq : forall n m, eqb n m = true -> n = m.
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

  
Lemma leb_lt : forall n m, leb n m = false -> le m n.
  actema.
Qed.


Inductive ll :=
  lnil
  | lcons : nat -> ll -> ll.

Definition low n l :=
  match l with
  | lnil => True
  | lcons m _ => le n m
  end.

 Fixpoint sorted l :=
  match l with
  | lnil => True
  | lcons n l => (low n l) /\ (sorted l)
  end.

Definition ifthl (b:bool) (n1 : ll) n2 :=
  if b then n1 else n2.

Fixpoint insert n l :=
  match l with
  | lnil => lcons n lnil
  | lcons m l' =>
      ifthl (leb n m)
       (lcons n l)
       ( lcons m (insert n l'))
  end.


Lemma insert_sort : forall n l, sorted l ->
                                sorted (insert n l) /\
                                  forall m, le m n /\ low m l -> low m (insert n l).
 generalize leb_le; intro h1.
 generalize leb_lt; intro h2.
 actema.
Qed.

Fixpoint insertion_sort l :=
  match l with
  | lnil => lnil
  | lcons n l => insert n (insertion_sort l)
  end.

Lemma sorted_insertion : forall l,
    sorted (insertion_sort l).
 pose proof insert_sort.
  actema.
Qed.


Definition ifthn (b:bool) (n1:nat) n2 :=
  if b then n1 else n2.

Fixpoint count n l :=
  match l with
  | lnil => 0
  | lcons m l =>
      ifthn (eqb n m)  (S (count n l))  (count n l)
  end.


                     
Lemma eqb_refl : forall n, eqb n n = true.
 generalize eqr_eqb; intro.
 generalize eqb_eqr; intro.
 generalize eqr_refl; intro.
  actema.
Qed.

Lemma leb_refl : forall n, leb n n = true.
  actema.
Qed.

          
Lemma count_i1 : forall n l, count n (insert n l) = S (count n l). 
generalize  eqb_refl; intro.
generalize leb_refl; intro.
actema.
Qed.


Lemma count_i2 : forall n m l, eqb m n = false -> count m (insert n l) = (count m l).
  actema.
Qed.


Lemma insertion_sort_count : forall a l, count a l = count a (insertion_sort l).
  pose proof count_i1.
  pose proof count_i2.
  pose proof eqr_eq.
  pose proof eqb_eqr.
  actema.
Qed.


Inductive Tree :=
  Leaf
| Node : nat -> Tree -> Tree -> Tree.

Definition hlow n t :=
  match t with
  | Node m _ _ => le n m
  | _ => True
  end.

Fixpoint Heap t :=
  match t with
  | Leaf => True
  | Node n t1 t2 =>
      Heap t1 /\ Heap t2
      /\ hlow n t1 /\ hlow n t2
  end.

Definition ift b (t1:Tree) t2 :=
  if b then t1 else t2.

Fixpoint hinsert n t :=
  match t with
  | Leaf => Node n Leaf Leaf
  | Node m t1 t2 =>
      ift (leb n m)
          (Node n (hinsert m t2) t1)
          (Node m (hinsert n t2) t1)
  end.

Lemma le_trans : forall a b c, le a b -> le b c -> le a c.
  actema.
Qed.

Lemma hl_trans : forall n m t,
    le n m -> hlow m t -> hlow n t.
  pose proof le_trans.
  actema.
Qed.

Lemma hinsert_heap :
  forall t n,
    Heap t ->
    Heap (hinsert n t)
    /\ (forall m, le m n -> hlow m t -> hlow m (hinsert n t)).
 generalize leb_le; intro h1.
 generalize leb_lt; intro h2.
pose proof hl_trans.
 actema.
Qed.

Fixpoint merge l1 :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | lnil, l => l
  | l, lnil => l
  | lcons a m1, lcons b m2 =>
      ifthl (leb a b)
          (lcons a (merge m1 l2))
          (lcons b (merge_aux m2))
  end
  in merge_aux.

Lemma merge_sorted : forall l2 l1,
    sorted l1 -> sorted l2 ->
    sorted (merge l1 l2)
    /\ (forall n, low n l1 -> low n l2 -> low n (merge l1 l2)).
Admitted.



Fixpoint to_heap l :=
  match l with
  | lnil => Leaf
  | lcons x l' => hinsert x (to_heap l')
  end.

Fixpoint to_list t :=
  match t with
  | Node x t1 t2 => lcons x (merge (to_list t1)(to_list t2))
  | Leaf => lnil
  end.

Definition heapsort l := to_list (to_heap l).

Eval compute in (heapsort (lcons 3 (lcons 0 (lcons 2 (lcons 1 lnil))))).

Lemma to_heap_heap : forall l, Heap (to_heap l).
  pose proof hinsert_heap.
  actema.
Qed.

Lemma to_list_sorted : forall t, Heap t -> sorted (to_list t)
                                                  /\ forall x, hlow x t -> low x (to_list t).
  pose proof merge_sorted.
  actema.
Qed.


Lemma heapsort_sorted : forall l, sorted (heapsort l).
  pose proof to_heap_heap.
  pose proof to_list_sorted.
 actema.
Qed.

Check count.
Fixpoint tcount n t :=
  match t with
  | Leaf => 0
  | Node m t1 t2 =>
      ifthn (eqb n m)
            (S (tcount n t1)+(tcount n t2))
            ((tcount n t1)+(tcount n t2))
  end.

Lemma tcount_hinsert :
  forall t a b,
    tcount a (hinsert b t) =
      ifthn (eqb a b)
            (S (tcount a t))
            (tcount a t).
  pose proof  eqb_refl.
  pose proof leb_refl.
   pose proof PeanoNat.Nat.add_succ_r.
  pose proof  PeanoNat.Nat.add_comm.

  actema.
Qed.

Lemma count_merge :
  forall n l1 l2,
    count n (merge l1 l2) = count n l1 + count n l2.
pose proof PeanoNat.Nat.add_0_r.
pose proof PeanoNat.Nat.add_succ_r.
move => n; elim => [|a l1 hl1]; elim => [|b l2 hl2]//=.

case: leb => //=;
 case e1: eqb; case e2: eqb => //=; rewrite ?hl2 ?hl1 //= ?e1 ?e2 ?PeanoNat.Nat.add_succ_r //=.
Qed.

Inductive isort : ll -> Prop :=
  sort_nil : isort lnil
| sort_cons : forall a n, isort n -> low a n -> isort (lcons a n).

  
Goal forall l, sorted l -> isort l.
  actema_force.
by constructor.
 constructor; auto.
by case H.


  (*
  induction t; simpl.
move => n m; by case: (eqb _ _).
move => a b.
  case  leb => /=.
  case ean: (eqb a n) => /=; move: (IHt2 a n); rewrite ean /= PeanoNat.Nat.add_comm;
move => -> //=;
rewrite  PeanoNat.Nat.add_succ_r //=.

 case eab: (eqb a b) => /=; move: (IHt2 a b);rewrite eab /= PeanoNat.Nat.add_comm;
move => -> //=;
rewrite  PeanoNat.Nat.add_succ_r //=;
case eqb => //=.
Qed.
 *)






=> IH.

  case e2 : eqb;  try rewrite (eqb_eq _ _ e2) //= ?eqb_refl //=; rewrite ?e2;
    case e3 : eqb; try rewrite (eqb_eq _ _ e3) //= ?eqb_refl //=;
  rewrite /= ?e2   /=;
  rewrite //=; try rewrite PeanoNat.Nat.add_comm //=;
 try (by rewrite (IHt2 _ _) (eqb_refl n) /= PeanoNat.Nat.add_succ_r);
try (by rewrite (IHt2 _ _) e3).
  case e4 : eqb; simpl;  try rewrite (eqb_eq _ _ e4) /=.
  move: (IHt2 n m); rewrite e4 ?(eqb_eq _ _ e4) /=;
   try move ->;
 rewrite ?PeanoNat.Nat.add_succ_r.
  Search (_ + (S _) = _ ).

  try (by rewrite (eqb_refl n) in e4);
     try (by rewrite e3 in e4).
by rewrite e3 in e4.


  Search eqb.

  Search (_+_ = _ + _).

  simpl.

  actema.

  actema.
