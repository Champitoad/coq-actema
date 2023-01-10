From Actema Require Import Loader.

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
  Check negb.
Lemma leb_gtb : forall n m, leb n m = negb (gtb n m).
actema_force "perf". 
Qed.

Fixpoint moins n m :=
  match m,n with
  | 0,_ => n
  | S m, S n => moins n m
  | S _, 0 => 0
  end.


(* bug: simplify peut toujours fabriquer des termes
 avec des match / fix *)
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

 Lemma le_trans : forall a b c, le a b -> le b c -> le a c.
actema.
Qed.

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
 generalize le_trans; intro h3.
actema.
Qed.
  

Fixpoint insertion_sort l :=
  match l with
  | lnil => lnil
  | lcons n l => insert n (insertion_sort l)
  end.

Lemma sorted_insertion : forall l,
    sorted (insertion_sort l).
 generalize insert_sort; intro h1.
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


Lemma eqr_eqb : forall n m, eqr n m -> eqb n m = true.
  actema.
Qed.

Lemma eqb_eqr : forall n m, eqb n m = true -> eqr n m.
  actema.
Qed.

Lemma eqr_refl : forall n, eqr n n.
actema.
Qed.

Lemma eqr_eq : forall n m, eqr n m -> n = m.
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
  induction l; simpl.
  Set Debug "backtrace".
actema_force.

  (* le DnD naturel ne marche pas, en revanche la tactique suivante
marche 
  actema. *)
move: (h1 n) => e.

  rew_dnd test e (@nil bool)
          (cons 0 (cons 0 nil))
          (@nil bool)
          (cons false nil)
          (@nil (option (inst1 test))).
done.
actema.
rewrite h1; reflexivity.
rewrite h1; reflexivity.
simpl; rewrite e0 IHl; reflexivity.  
rewrite e0 IHl; reflexivity.
Qed.

Lemma count_i2 : forall n m l, eqb m n = false -> count m (insert n l) = (count m l).
  induction l; simpl; move => e; rewrite /= ?e /=.
  reflexivity.
case ee : leb => /=.
rewrite e /=.
done.
case eqb => /=; rewrite IHl; done.
Qed.

Lemma insertion_sort_count : forall a l, count a l = count a (insertion_sort l).
  induction l.
    done.
  simpl.
  case e : (eqb a n).
  move: (eqb_eqr _ _ e) => e1.
  move: (eqr_eq _ _ e1) => <-.
  by rewrite count_i1 -IHl.
rewrite count_i2.
  by rewrite IHl.  
done.
Qed.

