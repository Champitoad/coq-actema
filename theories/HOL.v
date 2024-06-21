From mathcomp Require Import ssreflect ssreflect.seq.


Inductive TDYN :=
  tDYN : Type -> TDYN.
Definition ls := seq TDYN.


Inductive DYN :=
  mDYN : forall T, T -> DYN.


(* extracts nth type from a signature *)
Fixpoint sl (l:ls)(n:nat){struct l} : Type :=
  match l,n with
  | nil, _ => unit
  | cons (tDYN s )  _, 0 => s
  | cons _ l, S n => sl l n
  end.



(* tuples of objects *)
Fixpoint ppp (ts : ls)(l : list nat) : Type :=
  match l with
  | nil => unit
  | cons n l =>  ((sl ts n) * (ppp ts l))%type
  end.


Fixpoint predt  (ts : ls)(la : list nat) : Type :=
  match la with
  | nil => Prop
  | cons t0 la => (sl ts t0) -> predt ts la
  end.

(*
Definition predt ts (l : list nat) :=
  (ppp ts l) -> Prop.
*)

(* Definition eq_arity : pst lsar.
exists (cons 0 (cons 0 nil)).
exact (@eq nat).
Defined.
*)

(* ce qui est donné *)
(* Definition sfo : FOsign.
exists lsar.
split.
exact (cons p_op (cons m_op nil)).
exact (cons eq_arity nil).
Defined.
*)
(* Definition ts (sl:FOsign) :=  let (ts, _) := sl in ts. *)
Definition wsort (ls:ls) n :=  sl ls n.



(* pour gérer les tests d'égalité et les coercions
  entre sortes *)
Lemma eqnqtdec : forall (n:nat) m,  ((n=m) + (n<>m))%type.
elim => [|n hn][|m];
   try (by left);
   try (by right).
case: (hn m) => [e|e]; [left|right].
  by rewrite e.
by injection.
Defined.

Lemma eqnqtdec_refl : forall n,
    eqnqtdec n n = inl(eq_refl n).
elim => [//=|n hn/=]; by rewrite hn.
Qed.

Lemma eqlqtdec : forall (l : list nat) m, ((l=m) + (l<>m))%type.
  elim => [| x l hl][|y m]; first by left; reflexivity.
  right; discriminate.
  right; discriminate.
  case: (eqnqtdec x y);
    last by move => ne; right; move =>  [e1 e2].  
move => xy; case: (hl m) => lm.
  left; by rewrite xy lm.
by right; move =>  [e1 e2].  
Defined.

Lemma eqlqtdec_refl : forall n,
    eqlqtdec n n = inl(eq_refl n).
elim => [//=|n l hl/=]; by rewrite eqnqtdec_refl hl.
Qed.

Definition sign := ((list nat) * (list nat) * nat)%type.

Lemma eqsqtdec : forall (s1 : sign) s2, ((s1=s2) + (s1<>s2))%type.
move => [[l11 l12] n1][[l21 l22] n2].
case: (eqnqtdec n1 n2) => nn; last by right; move => [_ e2].
case:  (eqlqtdec l11 l21) => l1; last by right; move => [e1 e2].
case:  (eqlqtdec l12 l22) => l2; last by right; move => [e1 e2].
by left; rewrite nn l1 l2.
Defined.

Lemma eqsqtdec_refl : forall n,
    eqsqtdec n n = inl(eq_refl n).
move => [[l1 l2] n]/=.
 by rewrite eqnqtdec_refl !eqlqtdec_refl /=.
Qed.

Section s_cx.

Variable ts : ls.

Print wsort.
Print sl.

(*
Definition nthc
           (c:seq nat)(p : ppp ts c)(n:nat): (wsort ts (nth 0 c n)).
move: n p. rewrite /wsort.
elim: c => [| t c rc] [|n] //=.  
- move => _ ; apply def.
- move => _ ; apply def.
- move => [x _]; exact x.
- move => [_ x]; exact (rc n x).
Defined.

Definition nths s (c:seq nat)(p : ppp ts c)(n:nat): (wsort ts s).
move: c p n.  elim => [| s1 n hn].
 move => *; apply def.
move => [x p][|i].
 exact (trs ts s1 s x).
exact (hn p i).
Defined.
 *)

(* focused propositions with n free variables *)
Inductive cx : (seq nat)  -> Type :=
| cTop : forall n,  cx n
| cBot : forall n,  cx n
| cNot : forall n,  cx n -> cx n
| Hole : forall n,  ((ppp ts n) -> Prop) -> (cx n)
| impr : forall n, ((ppp ts n) -> Prop) -> (cx n) -> (cx n)
| impl : forall n, (cx n) -> ((ppp ts n) -> Prop) -> (cx n)
| orr : forall n, ((ppp ts n) -> Prop) -> (cx n) -> (cx n)
| orl : forall n, (cx n) -> ((ppp ts n) -> Prop) -> (cx n)
| andr : forall n, ((ppp ts n) -> Prop) -> (cx n) -> (cx n)
| andl : forall n, (cx n) -> ((ppp ts n) -> Prop) -> (cx n)
| fa : forall n s, (nat->nat) -> cx (cons s n) -> cx n
| ex : forall n s, (nat->nat) -> cx (cons s n) -> cx n
| equality : forall n s,
    ((ppp ts n) -> (wsort ts s)) ->((ppp ts n) -> (wsort ts s)) -> cx n
| property  : forall n s,
    ((ppp ts (cons s n)) -> Prop) ->
    ((ppp ts n) -> (wsort ts s))  -> cx n.

  Let pp := ppp ts.

(* constant cx's *)
Fixpoint ppc (P:Prop)(n : seq nat): (pp n) -> Prop :=
  match n with
  | nil => fun _ =>  P
  | cons s l => fun (c:(pp(cons s  l))) =>
             match c with
               pair _ d =>  (ppc P l d)
             end
  end.

Lemma ppce : forall P n c,  ppc P n c = P.
  move=> P; elim => [//=|s l hl][c1 c2]/=.
  by rewrite hl.
Qed.


(* translating back into Prop *)

Fixpoint coerce  n (c:cx n) : (pp n) -> Prop :=
  match c with
| cTop _ => ppc True _
  | cBot _ => ppc False _
  | cNot _ c => fun x => ~(coerce _ c x)
| Hole _ P => P
| impl _ c P => fun x => ((coerce _ c x)  -> (P x))
| impr _ P c => fun x =>  (P x) -> (coerce _ c x)
| orl _ c P => fun x => (coerce _ c x)\/(P x)
| orr _ P c => fun x =>  (P x) \/ (coerce _ c x)
| andl _ c P => fun x => (coerce _ c x) /\ (P x)
| andr _ P c => fun x =>  (P x) /\ (coerce _ c x)
| fa _ s _ c => fun  x =>  forall p:_, (coerce _ c (p, x))
| ex _ s _ c => fun  x =>  exists p:_,  (coerce _ c (p, x))
| equality _ _ t u =>fun x =>
                       (t x) = (u x)
| property _ _ P t => fun x =>
                        ( P ((t x), x))
end.


(* two tests to avoid too dependent types *)

Definition cT n (c:cx n) :=
  match n, c with
  | _, cTop _ => true
  | _, _ => false
  end.

Definition cB  n (c:cx n) :=
  match n, c with
  | _, cBot _ => true
  | _, _ => false
  end.

Lemma cTc : forall n c,
    cT n c = true -> c = cTop n.
by induction c.
Qed.
Lemma cBc : forall n c,
    cB n c = true -> c = cBot n.
by induction c.
Qed.


(* performing simplifications *)

Fixpoint simpl l (c : cx l) : cx l :=
  match l, c with
  | n, orr _ A B =>
      match (simpl _ B) with
      | cTop _ => cTop _
      | cBot _ => Hole _ A
      | B' => orr _ A B'
      end

  | n, orl _ A B =>
      match (simpl _ A) with
      | cTop _ => cTop _
      | cBot _ => Hole _ B
      | A' => orl _ A' B
      end

 | n, andl _ A  B =>
      match (simpl _ A) with
      | cTop _ => Hole _ B
      | cBot _ => cBot _
      | A' => andl _ A' B
      end
  | n, andr _ A B =>
      match (simpl _ B) with
      | cTop _ => Hole _ A
      | cBot _ => cBot _
      | B' => andr _ A B'
      end

  | n, impl _ A B =>
      match (simpl _ A) with
      | cTop _ => Hole _ B
      | cBot _ => cTop _
      | A' => impl _ A' B
      end

  
  | n, impr _ A B =>
      match (simpl _ B) with
      | cTop _ => cTop _
      | B' => impr _ A B'
      end
      
  | n, fa n' s t A =>
      match (cT (cons s n') (simpl (cons s n') A)) with
      | true => cTop  n'
      | _ => fa n' s t (simpl (cons s n') A)
      end
  | n, ex n' s t A =>
      match (cB (cons s n') (simpl (cons s n') A)) with
      | true => cBot n'
      | _ => ex n' s t (simpl (cons s n') A)
      end
  | n, cNot _ c =>
      match (simpl _ c) with
      | cTop _ => cBot _
      | cBot _ => cTop _
      | c' => cNot _ c'
      end
  | n, cBot _ => cBot _
  | n, cTop _ => cTop _
  | n, h => h
  end.

(* We need to show equivalence first *)

Lemma simpl_corr : forall n c i,
    coerce n c i <-> coerce n (simpl n c) i.
Proof.
move=> m c.
elim: {m} c  =>
        [n|n|n B hB|n P|n A B hB|n A hA B|n A  B hB|n A hA  B
        |n A B hB|n A hA B|n s nv A hA |n s nv A hA|n t u|n P t] i //=;
  split => h; try (move: (hA i) => [hA1 hA2]);
  try (move: (hB i) => [hB1 hB2]);           
  try ( move: h hA1 hA2;
        induction (simpl n A);
        rewrite /= ?ppce; intuition;
        rewrite ppce //=);
 try (move: h hB1 hB2;
  induction (simpl n B);rewrite /= ?ppce; intuition;
   rewrite ppce //=).
- case e: cT => //=; first
    by rewrite ppce.
  by move => p; case: (hA (p,i)); auto.
- move: h;   case e: cT => //=;
   last by move => h p; case: (hA (p,i)); auto.
  move => _ p; move: (hA (p,i)); rewrite (cTc _ _ e) /= ppce.
  by case; auto.  
- move: h => [p h];
  case e: cB => //=;
    first by case: (hA (p,i)); rewrite (cBc _ _ e) /= ppce; auto.
 exists p; case: (hA (p,i)); auto.
- move: h;   case e: cB => //=;
   first by rewrite ppce.
move=> [p h]; exists p; case: (hA (p,i)); auto.
Qed.  


Lemma simpl_step :  forall n c i,
    coerce n (simpl n c) i -> coerce n c i.
by move => n c i; case (simpl_corr n c i).
Qed.

Lemma simpl_fstep :  forall n c i,
     coerce n c i -> coerce n (simpl n c) i.
by move => n c i; case (simpl_corr n c i).
Qed.


Print pp.


Check sl.

Parameter apply_inst : forall
  (s1 s2 : list nat) (sr : nat)
  (s1' s2' : list nat) (sr' : nat) , sl ts sr'.

(*
Definition apply_inst s1 s1' s2 s2' sr sr' o1 o2 :=
  fun f : (pp s1) -> (pp s2) -> sl ts sr =>
    match
      eqlqtdec s1 s1', eqlqtdec s2 s2', eqnqtdec sr sr'
  with
  | inl e1, inl e2, inl er  =>
      
  | _ => None                                                      
    end.
*)
(* will indicate which deep operations to perform *)
Definition trace := (list bool).



(*
(* to avoid problems with type dependency *)

Fixpoint convert n m (i: pp n) : pp m :=
  match n, i, m with
  | nil, tt, m => (defs m)
  | cons s n, i, nil => (defs nil)
  | cons s1 n, (x,i), cons s2 m => (trs ts s1 s2 x, (convert n m i))
  end.


Lemma convert_corr : forall l i,  convert l l i = i.
  elim => [[]|x l hl[a b]]//=.
  by rewrite trs_corr hl.
Qed.
 *)


(* The result type of interactions (deep inference) *)

Inductive o3 : Type :=
  Hol3 : Prop -> o3
| top3
| bot3
| not3 : o3 -> o3
| impl3 : o3 -> Prop -> o3
| impr3 : Prop -> o3 -> o3
| orl3 : o3 -> Prop -> o3
| orr3 : Prop -> o3 -> o3
| andr3 : Prop -> o3 -> o3
| andl3 : o3 -> Prop -> o3
| fa3 : forall s, (nat->nat) -> (wsort ts s -> o3) -> o3
| ex3 : forall s, (nat->nat) -> (wsort ts s -> o3) -> o3.

(* translating into Prop *)
Fixpoint tr3 o :=
  match o with
  | Hol3 P => P
  | impl3 o P =>
      (tr3 o)->P
  | impr3 P o => P->(tr3 o)
  | orl3 o P => (tr3 o)\/P
  | orr3 P o => P\/(tr3 o)
  | andl3 o P => (tr3 o)/\P
  | andr3 P o => P/\(tr3 o)
  | fa3 s _ p =>  forall n,   (tr3 (p n))
  | ex3 s _ p => exists n, (tr3 (p n))
  | top3 => True
  | bot3 => False
  | not3 p => ~tr3 p
  end.


Lemma tH : forall P,  tr3 (Hol3 P) = P.
done.
Qed.

Lemma til : forall o P,  tr3 (impl3 o P) = ((tr3 o) -> P).
  done. Qed.



(* the datatype which will indicate whether encoutered quantified
   variables are instantiated and by what *)

Definition ct := seq nat.


  
(* the main functions as described in our CPP 2022 article *)
(* "side conditions" are generated (which are actually in the center
   and not on the side) : 
    - A->B  for the focused formulas (meant to be A->A in practice)
    - two equalites for equality rewrites which should be two trivial
      reflexive equalities
 *)


(*
Definition test (nh:ct)(hyp : cx nh)(hi : xx nh)
           : o3 :=
  match hyp in (cx nh), hi  return o3 with
  | Hole hh h, hi => Hol3 (h hi)
  | _, _ => bot3
  end. 
*)

Definition eq_nat :  forall n m : nat, option (n=m).
elim => [|n hn][| m]; first by  apply Some;  apply refl_equal.
 - apply None.
 - apply None. 
case: (hn m) => [e|].
 apply Some; rewrite e; apply refl_equal.
apply None.
Defined.

Lemma eq_nat_refl : forall n,  eq_nat n n = Some eq_refl.
 by elim => [|n //= ->]//=.
Qed.

Definition check_nat (T : nat -> Type)(n m : nat):
           T n -> option (T m).
case (eq_nat m n) => [e |]; last by intros; apply None.
move => t; apply Some; rewrite e; exact t.
Defined.

Lemma check_nat_refl : forall T n t, check_nat T n n t = Some t.
by move => T n t; rewrite /check_nat eq_nat_refl.
Qed.

Lemma nat_neq : forall n m, n<>m -> eq_nat n m = None.
elim => [|n hn][| m]//=.
move => nm.
have  ne: (n<>m) by move => e; apply nm; rewrite e.
by rewrite (hn m ne).
Qed.


Lemma check_nat_neq  T : forall n m t, n<>m -> check_nat T m n t = None.
by move => n m t nm; rewrite /check_nat nat_neq.
Qed.

Lemma check_nat_neq'  T : forall n m t, m<>n -> check_nat T m n t = None.
 move => n m t nm; rewrite /check_nat nat_neq //=.
by move => e; apply nm; rewrite e.
Qed.


Eval compute in (check_nat (fun _ => nat) 4 3 99).

Definition eq_list  :
  forall l m : list nat,
           option (l=m).
elim => [|x l hl][|y m].
- apply Some; apply refl_equal.
- apply None.
- apply None.
case (hl m) => [el |]; last by apply None.
case (eq_nat x y) => [ex |]; last by apply None.
rewrite el ex; apply Some; apply refl_equal.
Defined.

Eval compute in (eq_list  (cons 3 (cons 5 nil))(cons 3 (cons 5 nil))  ).

Lemma eq_list_refl : forall l, eq_list l l = Some eq_refl.
   by elim => [|x l //= ->]//=; rewrite eq_nat_refl.
Qed.

Definition check_list (T : list nat -> Type)l m: T l -> option (T m).
 case (eq_list m l) => [e |]; last by intros; apply None.
move => t; apply Some; rewrite e; exact t.
Defined.

Eval compute in (check_list  (fun _ => nat)  (cons 3 (cons 5 nil))(cons 3 (cons 5 nil)) 98).

Lemma check_list_refl : forall T l t, check_list T l l t = Some t.
  by move => T l t; rewrite /check_list eq_list_refl.
Qed.

Fixpoint ty_curry (T: nat -> Type) l r : Type :=
  match l with
  | nil => T r
  | cons n l => (T n) -> (ty_curry T l r)
  end.
Check ppp. Check (sl ts). 
Print unit.


Fixpoint app_curry (l : seq nat) (r:nat) : (ty_curry (sl ts) l r) -> 
                                (ppp ts l)-> (sl ts r) :=
  match l return (ty_curry (sl ts) l r) -> 
                 (ppp ts l)-> (sl ts r)
  with
  | nil => fun f a => f 
  | cons n l =>
      fun f a =>
        match a with
        | (x, a) =>
            app_curry l r (f x) a
        end
  end.

Definition check_curry l1 l2 r1 r2 (f : ty_curry (sl ts) l1 r1)(a : ppp ts l2) :
  option (sl ts r2).
case (check_list _ _ l1 a) => [b |]; last by apply None.
case (check_nat _ _ r2 (app_curry _ _ f b)) => [c|]; last by apply None.
apply Some; exact c.  
Defined.

Lemma check_curry_refl  l r f a :
    check_curry l l r r f a =
      Some (app_curry _ _ f a).
by rewrite /check_curry check_list_refl check_nat_refl.
Qed.


Inductive inst1 :=
  insti : forall (r:nat)(n : ct),(ty_curry (sl ts) n r) -> inst1.

(* Definition inst2 := {s & {n1 : ct & {n2 : ct & (pp n1)->(pp n2) -> sl ts s}}}. *)


Definition inst  :=
  list (option inst1).

(*
Fixpoint restrip (l : list (option inst2)) :=
  match l with
  | cons None l => cons None (restrip l)
  | cons (Some (existT s
                       (existT n1
                               (existT n2 f)))) l =>
      cons (Some (insti s n1 n2 f)) (restrip l)
  | nil => nil
  end.

    (option
       {s & {n1 : ct & {n2 : ct & (pp n1)->(pp n2) -> sl ts s}}}).
*)


(* Parameter apply_inst : forall
  (s1 s2 : list nat) (sr : nat)
  (s1' s2' : list nat) (sr' : nat) , sl ts sr'.
 *)

(*
Definition switch_inst1 i :=
  match i with
  | insti s n1 n2 f =>
      insti s n2 n1 (fun p1 p2 => f p2 p1)
  end.
*)
(* {s & {n1 : ct & {n2 : ct & (pp n1)->(pp n2) -> sl ts s}}}
           -> 
           {s & {n1 : ct & {n2 : ct & (pp n1)->(pp n2) -> sl ts s}}}
.

move => [s [n1 [n2 f]]].
exists s; exists n2; exists n1.
move => p2 p1; exact (f p1 p2).
Defined. *)

(*
Fixpoint switch_inst (i:inst) : inst :=
  match i with
  | cons None j => cons None (switch_inst j)
  | cons (Some h) j => cons (Some (switch_inst1 h))
                            (switch_inst j)
  | x => x
  end.
*)
Definition xor b b' :=
  match b, b' with
  | true, true => false
  | false, false => false
  | _, _ => true
  end.

Definition xx := pp.

Fixpoint ppconcat  n1 n2 : (ppp  ts n1) -> (ppp  ts n2) -> ppp ts (n1++n2) :=
  match n1  with
  | nil => fun _ i2 => i2
  | cons s1 n1 =>
      fun i1 i2 =>
        match i1 with
        | (x1, i1) =>
            (x1, (ppconcat n1 n2 i1 i2))
        end
  end.



Fixpoint b3 (rw:bool)(l:trace) (b:bool)(ist:inst)(nh:ct)(hyp : cx nh)(hi : pp nh)
         (ng : ct)(goal : cx ng)(gi : pp ng) : o3 :=
  match l  with
   | nil =>
         match  hyp in (cx nh), goal in (cx ng), hi, gi
                return o3 with
         | (Hole _ h), (Hole _ g), hi, gi =>
             (Hol3  ((h hi) ->
                     (g  gi)))
     | (equality nh' s' t u), (property ng' s P v), hi1, gi1 =>
         if rw
         then
           match (check_nat _ s s' (v gi1)), (check_nat _ s' s (t hi1))
           with
           | Some v', Some t' =>
               andl3
                 (Hol3 ((u hi1) = v'))
                 (P (t', gi1))
           | _,_ => bot3
           end
         else
          match (check_nat _ s s' (v gi1)), (check_nat _ s' s (u hi1))
           with
           | Some v', Some u' =>
               andl3
                 (Hol3 ((t hi1) = v'))
                 (P (u', gi1))
           | _,_ => bot3
           end
         | _,_,_,_=> bot3
         end
  | (cons x l) => 
     match x with
     | true => 
         match goal, ng, gi with
         | (impl ngg h B), ng', gi' =>
             (impl3 (f3 rw l b ist nh hyp hi ng' h gi')
                    (B gi'))
         | cNot ng1 hg, _, gi1 =>
              not3
               (f3 rw l b ist nh hyp hi
                   ng1 hg gi1) 
         | (impr ng'  B g), ng'', gi' =>
             (impr3 (B gi')
                  (b3 rw l b ist nh hyp hi ng' g gi'))
         | orl ng' g B, ng'', gi' =>
             orl3 (b3 rw l b ist nh hyp hi ng' g gi')
                    (B gi')
         | orr ng' B g, ng'', gi' =>
               orr3  (B  gi')
                     (b3 rw l b ist nh hyp hi ng' g gi')
         | andl ng' g B, ng'', gi' =>
             andl3 (b3 rw l b ist nh hyp hi ng' g gi')
                   (B gi')
         | andr ng' B g, ng'' , gi'=>
             andr3  (B gi')
                 (b3 rw l b ist nh hyp hi ng' g gi')
         |  (fa ng' s nv g), ng'', gi' =>
              fa3 s nv (fun n=>
                          (b3 rw l b ist nh hyp hi (cons s ng') g
                              (n, gi')))
         | ex ng' s nv g, ng2, gi1 =>
             match ist with
             | cons (Some (insti s' n f)) ist =>
                       if b then
                        match (check_curry _ _ _ s f (ppconcat _ _ gi1 hi))
                         with
                         | None => bot3
                         | Some r =>
                             b3 rw l b ist nh hyp hi _ g (r, gi1)
                         end
                       else
                         match (check_curry _ _ _ s f (ppconcat _ _ hi gi1))
                         with
                         | None => bot3
                         | Some r =>
                             b3 rw l b ist nh hyp hi _ g (r, gi1)
                         end
             |  cons None ist =>
                  ex3 s nv
                      (fun p =>
                         b3 rw l b ist nh hyp hi
                            (cons s ng') g
                            (p,  gi))
             | nil => bot3
          end  
                
      | cTop _, _, _ => top3
                     
      | cBot _, _, _ => bot3  
      | Hole _ _, _, _ => bot3
      | equality _ _ _ _, _, _ => bot3
      | property _ _ _ _, _, _ => bot3
  end  
  | false =>
      match hyp, nh, hi with
      | andl _ h B, nh1, hi1 =>
           (b3 rw l b ist nh1 h hi1
               ng goal gi)
      | andr _ B h, nh1, hi1 =>
                 (b3 rw l b ist nh1 h hi1
                     ng goal gi)
      | orl _  h B, nh1, hi1 =>
          andl3 (b3 rw l b ist nh1 h hi1
                   ng goal gi)
               ((B hi1)->
                (coerce ng goal gi))
      | orr _ B h, nh1, hi1 =>
          andr3 ((B hi1)->
                (coerce ng goal gi))
               (b3 rw l b ist nh1 h hi1
                   ng goal gi) 
      | impr _ B h, nh1, hi1 =>
          andr3 (B hi1)
                (b3 rw l b ist nh1 h hi1
                   ng goal gi)
      | impl  _ h B, _, _  => bot3            
      | cNot _ _, _, _  => bot3
      | cTop _, _, _  => bot3
      | cBot _, _, _  => top3
      | Hole _ _, _, _  => bot3

                     
      | fa _ s nv h, nh1, hi1 =>
          match ist with
          | cons None ist =>
              ex3 s nv
                  (fun p =>
                     (b3 rw l b ist
                         (cons s _) h
                                  (p, hi1))
                       ng goal gi)
          

          | cons (Some (insti s' n' f)) ist =>
              if b
              then 
               match (check_curry _ _ _ s f (ppconcat _ _ gi hi1)) with
                | None => bot3
                | Some r =>
                    b3 rw l b ist
                       _
                       h
                       (r, hi1)
                       ng goal gi
               end
              else
                match (check_curry _ _ _ s f (ppconcat _ _ hi1 gi)) with
                | None => bot3
                | Some r =>
                    b3 rw l b ist
                       _
                       h
                       (r, hi1)
                       ng goal gi
                       
                end
          | _ => bot3
          end
      | ex n s nv h, nh1, hi1 =>
          fa3 s nv
            (fun p =>
               (b3 rw l b ist
                   _ h
                   (p, hi1)
                   ng goal gi))

      | _, _, _ => bot3
         end
   end
  end
with f3 (rw:bool)(l:trace)(b:bool)(ist: inst)(n1:ct)(h1 : cx n1)(i1 : pp n1)
        (n2 : ct)(h2 : cx n2)(i2 : pp n2) :
      o3 :=
  match l with
  | nil =>
      match h1, h2, i1, i2 with
      | equality n1' s1 t u, property n2' s2 P v, hi3, hi4 =>(
          if rw then
            match (check_nat _ s2 s1 (v hi4)), (check_nat _ s1 s2 (t hi3))
            with
            | Some v', Some t' =>
                impl3
                  (Hol3 ((u hi3) = v'))
                  (P (t', hi4))
            | _,_ => top3
            end
          else
          match (check_nat _ s2 s1 (v hi4)), (check_nat _ s1 s2 (u hi3))
          with
          | Some v', Some u' =>
              impl3
                (Hol3 ((t hi3) = v'))
                (P (u', hi4))
          | _, _ => top3
          end)
            
      | property n2' s2 P v, equality n1' s1 t u, hi3, hi4 => (
          if rw then
            match (check_nat _ s2 s1 (v hi3)), (check_nat _ s1 s2 (t hi4))
            with
            | Some v', Some t' =>
                impl3
                  (Hol3 ((u hi4) = v'))
                  (P (t', hi3))
            | _,_ => top3
            end
         else
            match (check_nat _ s2 s1 (v hi3)), (check_nat _ s1 s2 (u hi4))
            with
            | Some v', Some u' =>
                impl3
                  (Hol3 ((t hi4) = v'))
                  (P (u', hi3))
            | _, _ => top3
            end )
      |  _, _, _, _ => top3
      end

  | cons x l =>
     match (xor x b) with
     | false => 
      match h1, n1, i1  with
      | andl n1' h1' B, n1, i1 =>
          andl3
            (f3 rw l b ist n1' h1' i1 n2 h2 i2)
            (B i1)
      | andr n1' B h1', n1, i1 =>
          andr3
            (B i1)
            (f3 rw l b ist n1' h1' i1 n2 h2 i2)
      | orl  n1' h1' B, n1, i1  =>
          orl3  (f3 rw l b ist n1' h1' i1 n2 h2 i2)
                (B i1)
      | orr n1' B h1', n1, i1  =>
          orr3 (B i1)
               (f3 rw l b ist n1' h1' i1 n2 h2 i2) 
      | impl n1' h1' B, n1, i1  =>
          impl3 (b3 rw l (negb b) ist n2 h2 i2 n1' h1'
                    i1)
                (B i1)
      | cNot n1' h1', n1, i1  =>
          not3
            (b3 rw l (negb b) ist n2 h2 i2 n1' h1'
                i1)
      | impr n1' B h1', n1, i1  =>
          impr3  (B i1)
                 (f3 rw l b ist n1' h1' i1 n2 h2 i2)
      | fa n1' s1 nv h1', n1, i1  =>
          match ist with
          | cons None ist =>
                fa3 s1 nv (fun n =>
                    (f3 rw l b ist (cons s1 n1') h1'
                         (n, i1)
                        n2 h2 i2))
          | cons (Some (insti s' n f)) ist =>
              match
                (if b
                 then (check_curry _ _ _ s1 f (ppconcat _ _ i2 i1))
                 else (check_curry _ _ _ s1 f (ppconcat _ _ i1 i2)))
              with
                | None => top3
                | Some r =>
                    f3 rw l b ist
                       _
                       h1'
                       (r, i1)
                       n2 h2 i2
                end
          | nil => top3
          end
      | ex n1' s1 nv h1', n1, i1  =>
          ex3 s1 nv
              (fun n =>
                 (f3 rw l b ist (cons s1 n1') h1'
                    (n, i1)
                    n2 h2 i2))
      | _, _, _ => top3
      end
   |  true  =>
       match h2, n2, i2 with
       | andl n2' h2' B, n2, i2  =>
           andl3 
             (f3 rw l b ist n1 h1 i1  n2' h2' i2)
             (B i2) 
       | andr n2' B h2', n2, i2  =>
           andr3
             (B i2) 
             (f3 rw l b ist n1 h1 i1 n2' h2' i2)
       | orl  n2' h2' B, n2, i2 =>
           orl3 
             (f3 rw l b ist n1 h1 i1 n2' h2' i2)
               (B i2) 
       | orr n2' B h2', n2, i2  =>
           orr3 (B i2)
                (f3 rw l b ist n1 h1 i1 n2' h2' i2) 
       | impl n2' h2' B, n2, i2  =>
           impl3 (b3 rw l b ist n1 h1 i1 n2' h2' i2)
                 (B i2)
       | cNot n2' h2', n2, i2  =>
           not3
             (b3 rw l b ist n1 h1 i1 _ h2'
                 i2)
      | impr n2' B h2', n2, i2  =>
          impr3  (B i2)
                 (f3 rw l b ist n1 h1 i1 n2' h2' i2 )
       | fa n2' s2 nv h2', n2, i2  =>
          match ist with
          | cons None ist =>
                fa3 s2 nv (fun n =>
                 (f3 rw l b ist n1 h1 i1
                     (cons s2 n2') h2'
                     (n, i2)
                 ))
          | cons (Some (insti s' n f)) ist =>
              match
                (if b
                 then (check_curry _ _ _ s2 f (ppconcat _ _ i2 i1))
                 else (check_curry _ _ _ s2 f (ppconcat _ _ i1 i2)))
              with
                | None => top3
                | Some r =>
                    f3 rw l b ist n1 h1 i1 _ h2' (r, i2)
                end
          | nil => top3
         end
       | ex n2' s2 nv h2', n2, i2  =>
           ex3 s2 nv
               (fun n =>
                  (f3 rw l b ist n1 h1 i1
                      (cons s2 n2') h2'
                   (n, i2)
                 )) 
      | _, _, _ => top3
      end
     end
  end.


Fixpoint bc3 (sh sg : nat)(rw:bool)(l:trace)
         (ist: list (option DYN))
         (b:bool)(nh:ct)(hyp : cx nh)
         (ng : ct)(goal : cx ng) :
  list (option (DYN * nat * nat)) := 
  match l  with
   | nil => nil
  | (cons x l) =>
     match x with
     | true => 
         match goal, ng with
         | (impl ngg h B), ng' =>
             fc3 sh sg rw l ist b nh hyp ng' h
         | cNot ng1 h, ng2 =>
               (fc3 sh sg rw l ist b  nh hyp ng2 h)
         | (impr ng'  B g), ng'' =>
                  (bc3 sh sg rw l ist b  nh hyp ng' g)
         | orl ng' g B, ng'' =>
             (bc3 sh sg rw l ist b  nh hyp ng' g)
         | orr ng' B g, ng'' =>
             (bc3 sh sg rw l ist b  nh hyp ng' g)
         | andl ng' g B, ng'' =>
             (bc3 sh sg rw l ist b nh hyp ng' g)
         | andr ng' B g, ng'' =>
             (bc3 sh sg rw l ist b nh hyp ng' g)
         |  (fa ng' s nv g), ng'' =>
                (bc3 sh (S sg) rw l ist b nh hyp (cons s ng') g)
         | ex ng' s nv g, ng2 =>
             match ist with
             | cons None ist =>
                 cons None
                      (bc3 sh (S sg) rw l ist b nh hyp
                     (cons s ng') g)
             | cons (Some f) ist =>
                 cons
                   (Some  (f, sh, sg))
                   (bc3 sh (S sg) rw l ist
                        b nh hyp
                        (cons s ng') g)
             | nil  =>
                 bc3 sh sg rw l ist b nh hyp
                     (cons s ng') g
             end
         | _, _ => nil
         end  
     | false =>
         match hyp, nh with
         | andl _ h B, nh1 =>
             (bc3 sh sg rw l ist b  nh1 h
                  ng goal)
         | andr _ B h, nh1 =>
                 (bc3 sh sg rw l ist b nh1 h ng goal)
         | orl _  h B, nh1 =>
             (bc3 sh sg rw l ist b nh1 h ng goal)
         | orr _ B h, nh1 =>
             (bc3 sh sg rw l ist b nh1 h ng goal) 
         | impr _ B h, nh1 =>
             (bc3 sh sg rw l ist b nh1 h ng goal)
         | fa _ s nv h, nh1 =>
             match ist with
             | cons None ist =>
                 cons None
                      (bc3 (S sh) sg rw l ist
                      b  _ h ng goal)
             | cons (Some f) ist =>
                 cons (Some (f, sh, sg))
                 (bc3  (S sh) sg rw l ist
                      b  _ h ng goal)
             | nil =>
                 (bc3 (S sh) sg rw l ist
                      b  _ h ng goal)
             end
         | ex n s nv h, nh1 =>
               (bc3 (S sh) sg rw l ist b  _ h ng goal)
         | _, _ => nil
         end
     end
  end
with fc3 (s1 s2 : nat)(rw:bool)(l:trace)(ist : list (option DYN))
         (b:bool)
         (n1:ct)(h1 : cx n1)
         (n2 : ct)(h2 : cx n2)
  : list (option (DYN * nat * nat)) :=
  match l with
  | nil => nil
  | cons x l =>
     match (xor x b) with
     | false => 
      match h1, n1 with
      | andl n1' h1' B, n1 =>
            (fc3 s1 s2 rw l ist b n1' h1' n2 h2)
      | andr n1' B h1', n1 =>
            (fc3 s1 s2 rw l ist b n1' h1' n2 h2)
      | orl  n1' h1' B, n1  =>
          (fc3 s1 s2 rw l ist b n1' h1' n2 h2)
      | orr n1' B h1', n1  =>
          (fc3 s1 s2 rw l ist b n1' h1' n2 h2) 
      | impl n1' h1' B, n1  =>
       (bc3 s2 s1 rw l ist (negb b) n2 h2 n1' h1')
      | cNot n1' h1', n1  =>
            (bc3 s2 s1 rw l ist (negb b) n2 h2 n1' h1')
      | impr n1' B h1', n1  =>
                 (fc3 s1 s2 rw l ist b n1' h1' n2 h2)
      | fa n1' so1 nv h1', n1  =>
          match ist with
          | cons None ist =>
              cons None
              (if b
               then
                 (fc3 s1 (S s2) rw l ist
                      b (cons so1 n1') h1' n2 h2)
               else
                 (fc3 (S s1) s2 rw l ist
                      b (cons so1 n1') h1' n2 h2))
          | cons (Some f) ist =>
              cons
                (Some (f, s1, s2))
                (if b
                 then
                   (fc3 s1 (S s2) rw l ist
                      b (cons so1 n1') h1' n2 h2)
                 else
                   (fc3 (S s1) s2 rw l ist
                        b (cons so1 n1') h1' n2 h2))
          | nil =>
              (fc3 (S s1) s2 rw l ist
                   b (cons so1 n1') h1' n2 h2)
          end             
      | ex n1' so1 nv h1', n1  =>
            (fc3 (S s1) s2 rw l ist b (cons so1 n1') h1' n2 h2)
      | _, _ => nil
      end
   |  true  =>
       match h2, n2 with
       | andl n2' h2' B, n2  =>
             (fc3 s1 s2 rw l ist b n1 h1  n2' h2')
       | andr n2' B h2', n2  =>
             (fc3 s1 s2 rw l ist b n1 h1 n2' h2')
       | orl  n2' h2' B, n2 =>
             (fc3 s1 s2 rw l ist b n1 h1 n2' h2')
       | orr n2' B h2', n2  =>
           (fc3 s1 s2 rw l ist b n1 h1 n2' h2') 
       | impl n2' h2' B, n2  =>
            (bc3 s1 s2 rw l ist (negb b) n1 h1 n2' h2')
       | cNot n2' h2', n2  =>
             (bc3 s1 s2 rw l ist b n1 h1 n2' h2')
       | impr n2' B h2', n2  =>
           (fc3 s1 s2 rw l ist b n1 h1 n2' h2')
       | fa n2' so2 nv h2', n2 =>
           match ist with
           | cons None ist =>
               cons None
                    (if b
                     then
                       (fc3 (S s1) s2 rw l ist
                            b n1 h1 (cons so2 n2') h2')
                     else
                       (fc3 s1 (S s2) rw l ist
                            b n1 h1 (cons so2 n2') h2'))
           | cons (Some f) ist =>
               cons
                 (Some (f, s1, s2))
                 (if b
                  then
                    (fc3 (S s1) s2 rw l ist
                        b n1 h1 (cons so2 n2') h2')
                  else
                    (fc3 s1 (S s2) rw l ist
                         b n1 h1 (cons so2 n2') h2'))
           | nil => nil
           end
       | ex n2' so2 nv h2', n2  =>
             (fc3 s1 (S s2) rw l ist b n1 h1 (cons so2 n2') h2')
       | _, _ => nil
      end
     end
  end.



(* The main lemma *)
Lemma bf3_corr :
  forall l,
    (forall fl b ist nh hyp hi ng goal gi,
         (tr3 (b3 fl l b ist nh hyp hi ng goal gi))
            -> (coerce _ hyp hi) -> (coerce _ goal gi))
    /\
      (forall fl b ist n1 h1 i1 n2 h2 i2,
          (coerce _ h1 i1) -> (coerce _ h2 i2) ->
          (tr3 (f3 fl l b ist n1 h1 i1 n2 h2 i2))).


elim => [//=|[|] l hl]/=; split; try done;
          try move: hl => [hl1 hl2].

-  move => [|] _ _
   [|s2 n2]
   [nh'|nh'|nh' P|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
       |nh' P h|nh' h P|s' nv nh' h|s' nv nh' h|nh' s' t u|nh s' P v] //= hi
   [|sg ng]
   [ng'|ng'|ng' Q| ng' Q|ng' Q g|ng' g Q|ng' Q g|ng' g Q
       |ng' Q g|ng' g Q|sg' nv ng' g|sg' nv ng' g|ng' s'' t' u'|ng' s'' P' v']
   gi //=;

   try (by 
   move: v' P';
   case: (PeanoNat.Nat.eq_dec s'' s') => [-> | se];
        move => v' P';
      try (by   rewrite !check_nat_refl /=;
                        move => [-> p] <-);
    try (by   rewrite !check_nat_refl /=;
                        move => [-> p] ->);
      try (by  rewrite (check_nat_neq' (wsort ts) _ _ _ se))).



   
- move => [|] _ _
   [|s2 n2]
   [nh'|nh'|nh' P|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
       |nh' P h|nh' h P|s' nv nh' h|s' nv nh' h|nh' s' t u|nh s' P v] //= hi
   [|sg ng]
   [ng'|ng'|ng' Q| ng' Q|ng' Q g|ng' g Q|ng' Q g|ng' g Q
       |ng' Q g|ng' g Q|sg' nv ng' g|sg' nv ng' g|ng' s'' t' u'|ng' s'' P' v']
   gi //=;
   try (move => -> p);
   try (move => p ->);
   try by(
     move: v' P' p;
       case: (PeanoNat.Nat.eq_dec s'' s') => [-> | se];
                                         move => v' P' p;
      try (by rewrite !check_nat_refl /=;   move => ->);
      try (by rewrite (check_nat_neq' (wsort ts) _ _ _ se)));
          
   try (by 
     move: t' u';
      case: (PeanoNat.Nat.eq_dec s'' s') => [-> | se];
                                         move => t' u';
       try (by rewrite !check_nat_refl /=;   move => ->);
       try (by rewrite (check_nat_neq (wsort ts) _ _ _ se))).

(try (by 
 move: t' u';
   case: (PeanoNat.Nat.eq_dec s'' s') => [-> | se];
                                         move => t' u';
   try (by rewrite !check_nat_refl /=;   move => ->);
   try (by rewrite (check_nat_neq (wsort ts) _ _ _ se)))).

  
(try (by 
 move: t' u';
   case: (PeanoNat.Nat.eq_dec s'' s') => [-> | se];
                                         move => t' u';
   try (by rewrite !check_nat_refl /=;   move => ->);
   try (by rewrite (check_nat_neq (wsort ts) _ _ _ se)))).

  
try (by 
 move: t' u';
   case: (PeanoNat.Nat.eq_dec s'' s') => [-> | se];
                                         move => t' u';
   try (by rewrite !check_nat_refl /=;   move => ->);
   try (by rewrite (check_nat_neq (wsort ts) _ _ _ se))).

try (by 
 move: t' u';
   case: (PeanoNat.Nat.eq_dec s'' s') => [-> | se];
                                         move => t' u';
   try (by rewrite !check_nat_refl /=;   move => ->);
   try (by rewrite (check_nat_neq (wsort ts) _ _ _ se))).

(try (by 
 move: t' u';
   case: (PeanoNat.Nat.eq_dec s'' s') => [-> | se];
                                         move => t' u';
   try (by rewrite !check_nat_refl /=;   move => ->);
   try (by rewrite (check_nat_neq (wsort ts) _ _ _ se)))).

(try (by 
 move: t' u';
   case: (PeanoNat.Nat.eq_dec s'' s') => [-> | se];
                                         move => t' u';
   try (by rewrite !check_nat_refl /=;   move => ->);
   try (by rewrite (check_nat_neq (wsort ts) _ _ _ se)))).

(try (by 
 move: t' u';
   case: (PeanoNat.Nat.eq_dec s'' s') => [-> | se];
                                         move => t' u';
   try (by rewrite !check_nat_refl /=;   move => ->);
   try (by rewrite (check_nat_neq (wsort ts) _ _ _ se)))).

(try (by 
 move: t' u';
   case: (PeanoNat.Nat.eq_dec s'' s') => [-> | se];
                                         move => t' u';
   try (by rewrite !check_nat_refl /=;   move => ->);
   try (by rewrite (check_nat_neq (wsort ts) _ _ _ se)))).



   move => [|] b ist nh hyp hi ng
          [ng'|ng'|ng' Q|ng' Q|ng' Q g|ng' g Q|ng' Q g|ng' g Q
              |ng' Q g|ng' g Q|ng' nv' sg' g|ng' nv' sg' g
          |ng' sg' t u|ng' s P v] gi //=;
          rewrite /= ?ppce //=; eauto;
            try (by move => [h|h]; eauto);
            try (by move => [h1 h2]; eauto). 

case: ist => [//=|[[sr nr gr]|] ist]//=.
case: b;
 case check_curry => //= ; eauto. 
move => [n hn]; eauto.


case: ist => [//=|[[sr nr gr]|] ist]//=.
case: b;
 case check_curry => //=; eauto.  
move => [n hn]; eauto.


  - move => fl [|] ist n1 h1 i1 n2 h2 i2 hr1 hr2.

   move: h1 i1 hr1 =>
        [nh'|nh'|nh' P|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
        |nh' P h|nh' h P|nh' s nw h|nh' s nw h|nh' s t u
        |nh' s P v] //= P1 i1;
       eauto;
   try (by case: i1; eauto);
  move: P1 i1 hr2 => i1 pv;
    try (by case:  ist => [|[f|] ist] //=; eauto);
    try (by move: IHh2; case:  ist => [|[f|] ist] //=; eauto);
    try (by case: pv => [p hp] c; exists p;
         eapply hl2; auto; auto).
    case: ist => [//=|[[s' n f]|//=] ist] //=; [|auto];
                 case check_curry => //= p2; eauto. 

 move: h2 i2 hr2 =>
        [nh'|nh'|nh' P|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
        |nh' P h|nh' h P|nh' s nw h|nh' s nw h|nh' s t u
        |nh' s P v] //= P2 i2;
       eauto;
   try (by case: i2; eauto).


    case: ist => [//=|[[sr nr  gr]|] ist]//=; last eauto.
 case check_curry => //= p2; eauto. 





  - move => fl [|] ist n1 h1 i1 n2 h2 i2 hr1 hr2;

 (   move: h1 i1 hr1 hr2=>
        [nh'|nh'|nh' P|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
        |nh' P h|nh' h P|nh' s nw h|nh' s nw h|nh' s t u
        |nh' s P v] //= P1 i1;
       eauto;
   try (by case: i1; eauto);
        move: P1 i1   => i1 pv; rewrite ?ppce //=; eauto;
    try (by case:  ist => [|[f|] ist] //=; eauto);
    try (by move: IHh2; case:  ist => [|[f|] ist] //=; eauto);
    try (by case: pv => [p hp] c; exists p;
                        eapply hl2; auto; auto);
                         try (case: pv => [p hp]);
    
        try (by move => [h'|h']; eauto);
            try (by move => [h1' h2']; eauto);

( move: pv;
    case: ist => [//=|[[sr nr  gr]|] ist]//=;
[  case check_curry => //= ; eauto|
move => [n hn]; eauto])).

  - move => fl [|] ist n1 h1 i1 n2 h2 i2 hr1 hr2.


    

 move: h2 i2 hr2 =>
        [nh'|nh'|nh' P|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
        |nh' P h|nh' h P|nh' s nw h|nh' s nw h|nh' s t u
        |nh' s P v] //= P2 i2;
       eauto;
   try (by case: i2; eauto).


    case: ist => [//=|[[sr nr gr]|] ist]//=; last eauto.
 case check_curry => //= ; eauto.

    
  move: h1 i1 hr1 hr2=>
        [nh'|nh'|nh' P|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
        |nh' P h|nh' h P|nh' s nw h|nh' s nw h|nh' s t u
        |nh' s P v] //= P1 i1;
       eauto;
   try (by case: i1; eauto);
        move: P1 i1   => i1 pv; rewrite ?ppce //=; eauto;
    try (by case:  ist => [|[f|] ist] //=; eauto);
    try (by move: IHh2; case:  ist => [|[f|] ist] //=; eauto);
    try (by case: pv => [p hp] c; exists p;
                        eapply hl2; auto; auto);
                         try (case: pv => [p hp]);
    
        try (by move => [h'|h']; eauto);
            try (by move => [h1' h2']; eauto).

move: pv;
    case: ist => [//=|[[sr nr1 nr2 gr]|] ist]//=; [|eauto].
case: check_curry; simpl; auto.
Qed.



Check bf3_corr.

Definition trl3 := nosimpl tr3.


(* The two actually used corollaries *)
Lemma b3_corr : 
    (forall (fl:bool) (l:trace) b  (ist : inst) (nh : ct)  (hi : pp nh)
            (ng : ct) (gi : pp ng)
            (hyp : cx nh)(goal : cx ng),
        trl3 (b3 fl l b ist nh hyp hi ng goal gi) ->
        coerce nh hyp hi -> coerce ng goal gi).
move => fl l b ist nh hi ng gi hyp goal.  
case: (bf3_corr l) => [h _]; apply h.
Qed.

(*
Axiom  b3'_corr :  forall l : trace,
    (forall fl (ist : inst) (nh : ct)  (hi : pp nh)
            (ng : ct) (gi : pp ng)
            (hyp : cx nh)(goal : cx ng),
        trl3 (b3' fl l ist nh hyp hi ng goal gi) ->
        coerce nh hyp hi -> coerce ng goal gi).
*)

  
Lemma f3_corr :
  forall (fl:bool) (l: trace) b (ist : inst) (n1 : ct) (h1 : cx n1) (i1 : pp n1) 
         (n2 : ct) (h2 : cx n2) (i2 : pp n2),
    coerce n1 h1 i1 ->
    coerce n2 h2 i2 ->
    trl3 (f3 fl l b ist n1 h1 i1 n2 h2 i2).
move => fl l b ist n1 h1 i1 n2 h2 i2.
case: (bf3_corr l) => [_ h]; apply h.
Qed.
Check fa.
(* The function instantiating an inner quantifier *)
Fixpoint instp (t:nat)(s : nat)(o : wsort ts s)(n : seq nat)
         (c : pp n)(h : cx n) : Prop :=
  match t with
  | 0 =>
      match h  with
      | fa m s' _ h' =>
          match check_nat _ s s' o
          with
          | Some o' =>
              match check_list _ n m c
              with
              | Some c' =>
                  coerce _ h' (o',c')
              |_ => True
              end
          | _ => True
          end
      | _ => True
      end
  | S t =>
      match h, c, n with
      | impl _ h' B, c, n =>
           (instn t s o _ c h')->
              (B c)
      | impr _ B h', c, n =>
          (B c) -> (instp t s o _ c h')
      | orl _ h' B, c, n =>
          ( instp t s o _ c h') \/(B c)
      | orr n' B h', c, n =>
           (B c) \/(instp t s o _ c h')
      |  andl _ h' B, c, n =>
          ( instp t s o _ c h') /\(B c)
      | andr _ B h', c, n =>
          (B c) /\(instp t s o _ c h')
      | fa _ s' _ h', c, n =>
          forall x : wsort ts s',
            ( instp t s o (cons s' n) (x,c) h')
     | ex _ s' _ h', c, n =>
          exists x : wsort ts s',
            ( instp t s o (cons s' n) (x,c) h') 
      | X, _, _ => True
      end
  end
with
instn (t:nat)(s : nat)(o : wsort ts s)(n : seq nat)
         (c : pp n)(h : cx n) : Prop := 
  match t with
  | 0 =>
      match h with
      | ex m s' _ h' =>
          match check_nat _ s s' o
          with
          | Some o' =>
              match check_list _ n m c
              with
              | Some c' =>
                  coerce _ h' (o',c')
              |_ => False
              end
          | _ => False
          end
      | _ => False
      end

  | S t =>
         match h, c, n with
      | impl n' h' B, c , n =>
           (instp t s o n' c h')->
              (B c)
      | impr n' B h', c , n =>
          (B c) -> (instn t s o n' c h')
      | orl n' h' B, c , n =>
          ( instn t s o n' c h') \/(B c)
      | orr n' B h', c , n =>
           (B c) \/(instn t s o n' c h')
      |  andl n' h' B, c , n =>
          ( instn t s o n' c h') /\(B c)
      | andr n' B h', c , n =>
          (B c) /\(instn t s o n' c h')
      | fa n' s' _ h', c , n =>
          forall x : wsort ts s',
            ( instn t s o (s'::n') (x,c) h')
      | ex n' s' _ h', c , n =>
          exists x : wsort ts s',
            ( instn t s o (s'::n') (x,c) h')
      | X, c , n => False
      end
  end.
   

Lemma inst_corr :
  forall t s o n h c,
 ((coerce n h c) ->  (instp t s o n c h))/\
   ((instn t s o n c h) -> (coerce n h c)).
  elim => [/=|t ht] s o n h.
- case: h => {n} n s' /=; rewrite ?ppce; auto; try done.
    move => _ h c.
    split; last done.
    move => hr.
    case (PeanoNat.Nat.eq_dec s' s) => [e | ne];
           last by rewrite (check_nat_neq (wsort ts) _ _ _ ne).
    move: h hr; rewrite e check_nat_refl check_list_refl; auto.
  
    move => _ h c.
    split; first done.
    move => hr.
  case (PeanoNat.Nat.eq_dec s' s) => [e | ne].
    move: h hr; rewrite e check_nat_refl check_list_refl; eauto.
  by move: hr; rewrite (check_nat_neq (wsort ts) _ _ _ ne).
- case: h =>    
          [n'|n'|n' h'|n' Q|n' Q h'|n' h' Q|n' Q h'|n' h' Q|
            n' Q h'|n' h' Q| n' s' nv h'|n' s' nv h'|n' s' t1 t2|
            n' s' Q t1] c; split; try (simpl; rewrite ?ppce; done);
     try (by move: (ht _ o _ h' c)=> [ht1 ht2]; rewrite /= ; auto; try tauto).  
 * move => h''; simpl in h''. move => x; move: (ht _ o _ h' (x,c)) => [ht1 ht2].
    auto.
 * move => h''; simpl in h''; move => x; move: (h'' x) => h2;
   by move: (ht _ o _ h' (x,c)) => [ht1 ht2]; apply ht2.
 * move => [x hx].
   exists x.
   by move: (ht _ o _ h' (x,c)) => [ht1 ht2]; auto.
 * move => [x hx].
   exists x.
   move: (ht _ o _ h' (x,c)) => [ht1 ht2]; auto.
Qed.

Lemma instp_corr t s o n h c:
 (coerce n h c) ->  (instp t s o n c h).
by case (inst_corr t s o n h c).
Qed.

Lemma instn_corr t s o n h c:
 (instn t s o n c h) ->  (coerce n h c).
by case (inst_corr t s o n h c).
Qed.





(* Socrates example *)
Parameter H M : nat -> Prop.

Definition hm := forall x,  H x -> M x.
Definition hs := H 0.
Definition gs := M 0.

Definition fhs := Hole (nil)  (fun _ => gs).


(*

Definition fgs := fa nil 0 (impr (cons 0 nil)
                             (fun x => let (n,_):=x in (H n))
                             (Hole (cons cnat nil) (fun x => let (n,_):=x in (M n)))).


Definition iS : inst.
  apply cons; try apply nil.
  apply Some.
  exists cnat; exists nil; exists nil => _ _; exact 0.
Defined.  

Eval compute in
  (trl3 (b3 (cons false (cons false nil)) iS nil fgs I nil fhs I)).

*)


(* two ways to get rid of the (Hol3 P->P) and
  replace it by top3 *)

 Fixpoint trex o :=
  match o with
  | Hol3 P => P
  | not3 o => trex o
  | impl3 o P =>
      (trex o)
  | impr3 P o => (trex o)
  | orl3 o P => (trex o)
  | orr3 P o =>(trex o)
  | andl3 o P => (trex o)
  | andr3 P o => (trex o)
  | fa3 s _ p =>  forall n,   (trex (p n))
  | ex3 s _ p => forall n, (trex (p n))
  | top3 => True
  | bot3 => False
  end.

 Fixpoint trexe o :=
  match o with
  | Hol3 P => False
  | not3 o => trexe o
  | impl3 o P =>
      (trexe o)
  | impr3 P o => (trexe o)
  | orl3 o P => (trexe o)
  | orr3 P o =>(trexe o)
  | andl3 (Hol3 e) P => e
  | andl3 o P => trexe o
  | andr3 P o => (trexe o)
  | fa3 s _ p =>  forall n,   (trexe (p n))
  | ex3 s _ p => forall n, (trexe (p n))
  | top3 => True
  | bot3 => False
  end.


Fixpoint o3_norm (o:o3) : o3 :=
  match o with
  | Hol3 P => top3
  | not3 o => not3 (o3_norm o)
  | impr3 B o => impr3 B (o3_norm o)
  | impl3 o B => impl3 (o3_norm o) B
  | andr3 B o => andr3 B (o3_norm o)
  | andl3 o B => andl3 (o3_norm o) B
  | orr3 B o => orr3 B (o3_norm o)
  | orl3 o B => orl3 (o3_norm o) B
  | fa3 s nv f => fa3 s nv (fun n => o3_norm (f n))
  | ex3 s nv f => ex3 s nv (fun n => o3_norm (f n))
  | x => x
  end.


Fixpoint o3_norme (o:o3) : o3 :=
  match o with
  | Hol3 P => top3
  | not3 o => not3 (o3_norme o)
  | impr3 B o => impr3 B (o3_norme o)
  | impl3 o B => impl3 (o3_norme o) B
  | andr3 B o => andr3 B (o3_norme o)
  | andl3 (Hol3 _) B => Hol3 B
  | andl3 o B => andl3 (o3_norme o) B
  | orr3 B o => orr3 B (o3_norme o)
  | orl3 o B => orl3 (o3_norme o) B
  | fa3 s nv f => fa3 s nv (fun n => o3_norme (f n))
  | ex3 s nv f => ex3 s nv (fun n => o3_norme (f n))
  | x => x
  end.

Fixpoint o3_id (o:o3) (Q:Prop) : Type :=
  match o with
  | Hol3 P => P = (Q->Q)
  | not3 o => o3_id o Q
  | impr3 _ o => o3_id o Q
  | impl3 o _ => o3_id o Q
  | andr3 _ o => o3_id o Q
  | andl3 o _ => o3_id o Q
  | orr3 _ o => o3_id o Q
  | orl3 o _ => o3_id o Q
  | fa3 s _ f => forall n,  o3_id (f n) Q
  | ex3 s _ f => forall n,  o3_id (f n) Q
  | top3 => True
  | bot3 => True
  end.

Lemma o3_norm_corr :
  forall Q o, (o3_id o Q) -> (tr3 o)<->(tr3(o3_norm o)).
  move=> Q.
  elim => [P|||o|o ho B|B o ho|o ho B|B o ho|o ho B|B o ho
          |s nv f hf|s nv f hf]=>/= h; split; auto; first (by rewrite h);
try          move: (ho h) => [h1 h2];
auto; try (by intuition);
try (by move => hn n; case: (hf n); auto);
move => [n hn]; case: (hf n); eauto.
Qed.



Lemma trex_norm_corr : forall o, (trex o) ->
                                 (tr3 o)<->(tr3(o3_norm o)).
elim => [P|||o|o ho B|B o ho|o ho B|B o ho|o ho B|B o ho
        |s nv f hf|s nv f hf]=>/= h; split;
        (try case (ho h) => h1 h2); auto;
        try  tauto;
        try (by move => hn n; case: (hf n); auto);
        move => [n hn]; case: (hf n); eauto.
Qed.


Lemma trex_norme_corr :
  forall o, (trexe o) -> (tr3 o)<->(tr3(o3_norme o)).
Proof.
elim => [P|||o|o ho B|B o ho|o ho B|B o ho|o ho B|B o ho
        |s nv f hf|s nv f hf]=>/= h; split;
        (try case (ho h) => h1 h2); auto;
        try  tauto;
        try (by move => hn n; case: (hf n); auto);
        try (by move: h o; case: B => //=; auto;tauto);
        move => [n hn]; case: (hf n); eauto.
Qed.


Lemma trex_norm_apply : forall o, (trex o) ->
                                  (trl3(o3_norm o)) -> (tr3 o).
move => o h1 h2; case: (trex_norm_corr o); auto.
Qed.


Lemma trex_norme_apply : forall o,  (trexe o) ->
                                    (trl3(o3_norme o)) -> (tr3 o).
move => o h1 h2; case: (trex_norme_corr o); auto.
Qed.

Lemma trex_norm_fapply : forall o, (trex o) ->
                                  (tr3 o) -> (trl3(o3_norm o)).
move => o h1 h2; case: (trex_norm_corr o) => //= h3 h4 ; apply h3; auto.
Qed.


Lemma trex_norme_fapply : forall o,  (trexe o) ->
                            (tr3 o)->  (trl3(o3_norme o)).
  move => o h1 h2.
  case: (trex_norme_corr o) => //= h3 h4; apply h3; auto.
Qed.

(* just to illustrate possible use *)


Lemma o3_norm_apply : forall o,
    {Q & o3_id o Q} -> (trl3 (o3_norm o)) -> (tr3 o).
move => o [Q eQ] h; case: (o3_norm_corr Q o); auto.
Qed.

(* with the second version *)
(*
Lemma ex1 : (tr3  (b3 (cons false (cons false nil)) iS nil fgs I nil fhs I)).
  apply o3_norm_apply;
    first by simpl; eauto.
  simpl.
Abort.

(* with the first version *)
Lemma ex1 : (tr3  (b3 (cons false (cons false nil)) iS nil fgs I nil fhs I)).
apply trex_norm_apply; first done.
simpl.
Abort.
*)



(* Tactics for reification *)



(* Definition dyn := {T:Type & T}. *)

Fixpoint tpp (l : seq Type) : Type :=
  match l with
  | cons T l =>  T * (tpp l)
  | _ => unit
  end.

  Inductive s3 : (seq Type) -> Type :=
  | box : forall n, (tpp n -> Prop) -> s3 n
  | t3 :  forall n, s3 n
  | bo3 : forall n, s3 n
  | n3 :  forall n, s3 n -> s3 n
  | i3 :  forall n, s3 n -> s3 n -> s3 n
  | d3 :  forall n, s3 n -> s3 n -> s3 n
  | c3 :  forall n, s3 n -> s3 n -> s3 n
  | fs3 : forall T n, (nat->nat) -> s3 (cons T n) -> s3 n
  | e3 : forall T n, (nat->nat) -> s3 (cons T n) -> s3 n
.


Fixpoint cs3 n (e: s3 n)(i:tpp n) : Prop :=
  match e,i with
  | box n p, i => p i
  | t3 _, i => True
  | bo3 _, i => False
  | n3 _ e, i => ~(cs3 _ e i)
  | i3 _ a b, i => (cs3 _ a i)->(cs3 _ b i)
  | c3 _ a b, i => (cs3 _ a i)/\(cs3 _ b i)
  | d3 _ a b, i => (cs3 _ a i)\/(cs3 _ b i)
  | fs3 s n' _ e, i => forall x: s,
      cs3 (cons s n') e (x,i)
  | e3 s n' _ e, i => exists x: s,
      cs3 (cons s n') e (x,i)
  end.

Definition eT n (c:s3 n) :=
  match n, c with
  | _, t3 _ => true
  | _, _ => false
  end.

Definition eB  n (c:s3 n) :=
  match n, c with
  | _, bo3 _ => true
  | _, _ => false
  end.


Lemma eTc : forall n c,
    eT n c = true -> c = t3 n.
by induction c.
Qed.
Lemma eBc : forall n c,
    eB n c = true -> c = bo3 n.
by induction c.
Qed.

Fixpoint simplc n (e : s3 n) : s3 n :=
  match e with
  | c3 _ a b =>
   match (simplc _ a) with
    | t3 _ => simplc _ b
    | bo3 _ => bo3 _
    | a' =>
        match simplc _ b with
        | t3 _ => a'
        | bo3 _ => bo3 _
        | b' => c3 _ a' b'
        end
   end
  | d3 _ a b =>
       match (simplc _ a) with
       | t3 _ => t3 _                    
       | bo3 _ => simplc _ b
       | a' =>
           match simplc _ b with
           | t3 _ => t3 _
        | bo3 _ => a' 
        | b' => d3 _ a' b'
        end
       end
  | i3 _ a b =>
      match (simplc _ a) with
      | bo3 _ => t3 _
      | t3 _ => (simplc _ b)
      | a' =>
          match (simplc _ b) with
          | t3 _ => t3 _
          | b' => i3 _ a' b'
          end
      end
  | fs3 s n' f a =>
      if (eT _ (simplc (s::n') a))
      then t3 n'
      else fs3 _ _ f (simplc _ a)
  | e3 s n' f a =>
           if (eB _ (simplc (s::n') a))
      then bo3 n'
      else e3 _ _ f (simplc _ a)
  | n3 c' a =>
      match simplc _ a with
      | t3 _ => bo3 _
      | bo3 _ => t3 _
      | a' => n3 c' a'
      end
  | box c p => box c p
  | t3 n' => t3 n'
  | bo3 n' => bo3 n'
  end.


Lemma simplc_corr : forall n e i,
    cs3 n e i <-> cs3 n (simplc _ e) i.
fix hr 2.
move => m.
move =>
       [n p|n|n|n a|n a b|n a b|n a b
       |s n f a|s n f a] i //= ;split => h;
   try (move: (hr _ a i) => [ha1 ha2]);
   try (move: (hr _ b i) => [hb1 hb2]);
   try (by
     induction (simplc n a); move: ha1 ha2 h; simpl; try tauto);
   try (by
     move: h;
     induction (simplc n a);
     induction (simplc n b);
     move: ha1 ha2 hb1 hb2; simpl; try tauto).
- case e : eT => //= x;
  move:  (hr _ a (x,i)) => [ha1 ha2]; auto.
- move: h; case e : eT => //= h x;
   move: (hr _ a (x,i))=>[ha1 ha2]; auto.
  move: (eTc _ _ e) ha1 ha2=> ->; auto.
- move: h=>[x hx].
  case e : eB; move: (hr _ a (x,i))=>[ha1 ha2];
    auto.
     move: (eBc _ _ e) ha1 ha2=> ->; eauto.
  exists x; auto.
- move: h; case e : eB => //=.
move => [x hx].
exists x.
move: (hr _ a (x,i)) => [ha1 ha2]; eauto.
Qed.

Lemma simplc_corrh n e i :
    cs3 n e i -> cs3 n (simplc _ e) i.
by case : (simplc_corr n e i).
Qed.


Lemma simplc_corrg n e i :
  cs3 n (simplc _ e) i ->  cs3 n e i.
by case : (simplc_corr n e i).
Qed.

End s_cx.


Ltac get_last_r x l :=
  match l with
  | nil => constr:(x)
  | cons ?y ?l' => get_last_r y l'
  end.

Ltac get_last l := get_last_r constr:(true) l.

Ltac snitch_last l :=
  match l with
  | nil => constr:(l)
  | cons _ nil => constr:(@nil bool)
  | cons ?x ?l' => let r := snitch_last l'
                     in constr:(cons x r)
  end.



Notation "'subst!' y 'for' x 'in' f" :=
 (match y with x => f end) (at level 10, f at level 200).

Ltac beta1 func arg :=
 lazymatch func with
 | (fun a => ?f) => constr:(subst! arg for a in f)
 end.


Check ltac:(let r := beta1 (fun x : nat => x = 4) (3+3) in exact r).


Ltac wrap names vals t :=
 lazymatch names with
 | nil => t
 | cons (mDYN ?UU ?y) ?ys =>
     constr:(
       let (v0, rest0) := vals
       in ltac:(
            let t' := wrap ys rest0 t in
            lazymatch eval pattern y in t' with
            | ?f y => let t'' := beta1 f v0 in exact t''
                        end))
 end.

Ltac detectTF t :=
  lazymatch t with
  | ?a -> ?b =>
      let ra := ltac:(detectTF a) in
      let rb := ltac:(detectTF b) in
      constr:(ra -> rb) 
  | ?a /\ ?b => 
      let ra := ltac:(detectTF a) in
      let rb := ltac:(detectTF b) in
      constr:(ra /\ rb) 
  | ?a \/ ?b =>
      let ra := ltac:(detectTF a) in
      let rb := ltac:(detectTF b) in
      constr:(ra \/ rb) 
  | ~ ?a =>
      let ra := ltac:(detectTF a) in
      constr:(~ ra)
  | forall x: ?T, @?body' x =>
          let y := fresh "y" in
          let nb :=
            constr:(fun y: T => ltac:(
              let body := beta1 body' y in
              let r := detectTF body
           in
           exact r))
          in
          let xx := fresh x 
          in constr:(forall xx:T,
                        ltac:( let r := beta1 nb xx in exact r))
  | exists  x: ?T, @?body' x =>
          let y := fresh "y" in
          let nb :=
            constr:(fun y: T => ltac:(
              let body := beta1 body' y in
              let r := detectTF
                      body
           in
              exact r))
          in
          let xx := fresh x in
          constr:(exists xx:T,
                        ltac:( let r := beta1 nb xx in exact r))
  | ?u =>
      let nu := eval compute in u in
        match nu with
        | True => True
        | False => False
        | _ => u
        end
end.



Ltac sreify_rec n env t :=
  let tTF := detectTF t in 
  match tTF with
  | True => constr:(t3 n)
  | False => constr:(bo3 n)
  | ?a -> ?b =>
      let ra := ltac:(sreify_rec n env a) in
      let rb := ltac:(sreify_rec n env b) in
      constr:(i3 n ra rb) 
  | ?a /\ ?b => 
     let ra := (sreify_rec n env a) in
      let rb := (sreify_rec n env b) in
      constr:(c3 n ra rb) 
  | ?a \/ ?b =>
      let ra := ltac:(sreify_rec n env a) in
      let rb := ltac:(sreify_rec n env b) in
      constr:(d3 n ra rb)
  | ~ ?a =>
      let ra := ltac:(sreify_rec n env a) in
      constr:(n3 n ra)

  | forall x: ?T, @?body' x =>
          let y := fresh "y" in
          lazymatch
            constr:(fun y: T => ltac:(
              let body := beta1 body' y in
              let r := sreify_rec
                      (@cons Type T n)
                      (cons (@mDYN T y) env)
                      body
           in
              exact r))
     with
     | (fun _: T => ?r) => constr:(fs3 T n (fun x:nat=> x) r) 
     end
  | exists x: ?T, @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: T => ltac:(
           let body := beta1 body' y in
           let r := sreify_rec
                      (@cons Type T n)
                      (cons (@mDYN T y) env)
                      body
           in
              exact r))
     with
     | (fun _: T => ?r) => constr:(e3 T n (fun x:nat=> x) r) 
     end
  | _ =>
      let z := fresh "z" in
          constr:(box n (fun (z: tpp n) =>
                   ltac:(let r := wrap env z t in
                                  exact r))) 

end.

Ltac orename o t' :=
  let oo := eval hnf in o in
    let t := eval hnf in t' in
  match oo with
  | not3 ?ts ?oa =>
      match t with
      | ~ ?ta =>
          let ra := orename oa ta in
          constr:(~ ra)
      end
  | impl3 ?ts ?oa ?P =>
      match t with
      | ?ta -> ?tb =>
          let ra := orename oa ta in
          constr:(ra -> tb)
      end
        
  | impr3 ?ts ?P ?ob =>
        match t with
      | ?ta -> ?tb =>
          let rb := orename ob tb in
          constr:(ta -> rb)
        end
  | orl3 ?ts ?oa ?P =>
      match t with
      | ?ta \/ ?tb =>
          let ra := orename oa ta in
          constr:(ra \/ tb)
      end
        
  | orr3 ?ts ?P ?ob =>
        match t with
      | ?ta \/ ?tb =>
          let rb := orename ob tb in
          constr:(ta \/ rb)
        end
  | andl3 ?ts ?oa ?P =>
      match t with
      | ?ta /\ ?tb =>
          let ra := orename oa ta in
          constr:(ra /\ tb)
      end
        
  | andr3 ?ts ?P ?ob =>
        match t with
      | ?ta /\ ?tb =>
          let rb := orename ob tb in
          constr:(ta/\ rb)
        end
  | fa3 ?ts ?s (fun x:_ => _) ?f =>
      match t with
      | forall y : ?U, ?body =>
            constr:(forall x:U,
                       ltac:( let r2 :=
                     orename constr:(f x)
                        constr:(subst! x for y in body)
                              in exact r2))
      | _ => constr:(0)
      end
  | ex3 ?ts ?s (fun x:_ => _) ?f =>
      let xx := fresh x in
      match t with
      | exists y : ?U, ?body =>
            constr:(exists xx:U,
                       ltac:( let r2 :=
                     orename constr:(f xx)
                        constr:(subst! xx for y in body)
                              in exact r2))
      end
  | Hol3 ?ts ?P => constr:(t)
  | _ => constr:(t')
  end.


Ltac srename s t :=
  match s with
  | i3 _ ?sa ?sb =>
      match t with
      | ?ta -> ?tb =>
          let ra := srename sa ta in
          let rb := srename sb tb in
          constr:(ra -> rb)
      end
  | c3 _ ?sa ?sb =>
      match t with
      | ?ta -> ?tb =>
          let ra := srename sa ta in
          let rb := srename sb tb in
          constr:(ra /\ rb)
      end
  | d3 _ ?sa ?sb =>
      match t with
      | ?ta -> ?tb =>
          let ra := srename sa ta in
          let rb := srename sb tb in
          constr:(ra \/ rb)
      end
  | n3 _ ?sa =>
      match t with
      | ~ ?ta =>
          let ra := srename sa ta in
         constr:(~ ra)
      end
  | fs3 _  _ (fun x:_ => _) ?sb =>
      match t with
      | forall y : ?U, ?body =>
          let r1 := constr:(
                        forall x:U,
                          ltac:(let r2 := srename
                                            sb
                                            (subst! x for y in body)
                                in exact r2) ) in
          r1
      end 
  | e3 _  _ (fun x:_ => _) ?sb =>
      match t with
      | exists y : ?U, ?body =>
          let r1 := constr:(
                       exists x:U,
                         ltac:(let r2 := srename
                                           sb
                                           (subst! x for y in body)
                               in exact r2) ) in
          r1
       end
  | _ => t
  end.


Ltac sreify_goal :=
  match goal with
  | |- ?g =>
      let r := sreify_rec  (@nil Type)  (@nil DYN)  g in
     change (cs3 nil r tt)
  end.

Ltac simplify_goal :=
  sreify_goal;
  apply simplc_corrg;
  rewrite /simplc /eB /eT;
  match goal with
  | |- (cs3 _ ?sg _) =>
      rewrite /cs3; try exact I;
      match goal with
      | |- ?pg =>
          let ng := srename sg pg in
          try change ng
      end
  end;
  try discriminate.

Ltac sreify_hyp h :=
  let g := type of h in
  let r := sreify_rec  (@nil Type)  (@nil DYN)  g in
  change (cs3 (@nil Type) r tt) in h.

Ltac simplify_hyp h :=
  sreify_hyp h;
  move: (simplc_corrh _ _ _ h);
  clear h;  move => h;
  rewrite /simplc /eB /eT in h;
  match type of h with
  | (cs3 _ ?sh _) =>
      rewrite /cs3 in h;
      match type of h with
      | ?ph =>
          let nh := srename sh ph in
          try change nh in h
      end
  end;
  try (elim h; fail);
  try discriminate.

(* debut modifs *)


Ltac nbargs t :=
  match t with
  | ?f _ => 1 + (nbargs f)
  | _ => 0
  end.

Ltac strip_arg t :=
  match t with
  | ?f _ => let r:= f in exact r
  end.

Ltac get_arg t :=
  match t with
  | _ ?f =>  let r:= f in exact r
  end.

Ltac eta :=
  match goal with
  | |- ?g =>
      change ((fun x => (ltac:(strip_arg g) x)) ltac:(get_arg g))
  end.

Ltac pat n p x:=
  match n with
  | O =>
      match p with
      | (?t ?a) => constr:(@pair _ _ (t x) a)
      end
  | S ?n' =>
      match p with
      | (?t ?a) => 
          let r := pat n' t in
          match r with
          | (?r', ?b) =>
              constr:(@pair _ _ (r' t) b)
          end
      end
  end.

Ltac patt n p :=
  let x := fresh "x" in
  match (pat n p x) with
  | (?f, ?a) => 
      constr:((fun x => f) a)
  end.

Ltac list_args_r t l :=
  match t with
  | (?f ?a) =>
      let A := type of a in
       list_args_r f (@cons DYN (mDYN A a) l)
  | ?t => 
      let T := type of t in
      constr:(cons (mDYN T t) l)
  end.

Ltac list_args t :=
  list_args_r t (@nil DYN).

Ltac extract t :=
  match t with
   | (mDYN _  ?f) => f
  end.

Ltac rebuild_r t l :=
  match l with
  | nil =>  t
  | (cons ?a ?f) =>
      let a' := extract a in
      let t' := constr:(t a') in
       (rebuild_r t' f)
  end.

Ltac id d := d.

Ltac app f x :=
  let g := extract f in
    constr:(g x).

Ltac rebuild t :=
  match t with
  | (cons ?f ?a) =>
      let f' := extract f in
       rebuild_r f' a
  end.

Ltac tnth l n :=
  match n with
    | O =>
      match l with
      | cons ?x _ => x
      | _ => 999
      end
  | S ?m =>
      match l with
      | cons ?x  ?l' =>
          tnth l' m
      end
  end.

Ltac exarg n t :=
  let l := list_args t in
  let r := (tnth l ((S n))) in
   r.

Ltac exargp p t :=
  match p with
  | cons ?n nil => exarg n t
  | cons ?n ?q =>
   let l := list_args t in
   let u := tnth l (S n) in 
   let v := extract u in 
   exargp q v
  end.

Ltac ttreplace d n l :=
  match l with
  | cons ?x ?l' =>
      match n with
      | 0 => constr:(cons d l')
      | S ?n' => let r := ttreplace d n' l' in
                constr:(cons x r)
      end
  end.

Ltac treplace d t p :=
    match p with
  | nil => d
  | cons 0 ?p' =>
      match t with
      | (?a ?b) =>
          let a' := treplace d a p' in
          constr:(a' b)
      | ?a -> ?b =>
          let a' := treplace d a p' in
          constr:(a' -> b)
      | forall x:?a, ?b =>
          let a' := treplace d a p' in
          constr:(forall x : a', b)
      | exists x:?a, ?b =>
          let a' := treplace d a p' in
          constr:(exists x : a', b)
      end
    | cons 1 ?p' =>
        match t with
        | (?a ?b) =>
            let b' := treplace d b p' in
            constr:(a b')
        | ?a -> ?b =>
            let b' := treplace d b p' in
            constr:(a -> b')
        | forall x:?a, ?b =>
          let b' := treplace d b p' in
          constr:(forall x : a, b')
        | exists x:?a, ?b =>
            let b' := treplace d b p' in
            constr:(exists x : a, b')
        end
    | _ => t
    end.
 
 (* old v 
Ltac treplace  d t p :=
  match p with
  | nil => d
  | cons ?n ?p' =>
      let l := list_args t in
      let t' := extract ltac:(tnth l (S n)) in
      let x' := treplace d t' p' in
      let l' :=  ttreplace constr:(mDYN _ x') (S n) l in
      let r := rebuild l'
      in r
end.
*)


Ltac find_pat t p :=
   match p with
  | nil => t
  | cons ?n ?p' =>
      let l := list_args t in
      let t' := extract ltac:(tnth l (S n)) in
      let x' := find_pat t' p' in
     x'
end.

Ltac buil_imp l :=
  match l with
    (cons ?a (cons ?b _)) =>
      let a' := extract a in
      let b' := extract b in
      constr:(a' -> b')
  end.

Definition imp_fun A B := A -> B.


(* Simplify the subterm at [path] in the term [t], and return the updated term. 
   [path] is a list of natural numbers. *)
Ltac simpl_path_r p t :=
  match constr:(pair p t) with
  (* Base case. *)
  | (nil, _) => eval simpl in t
  (* Lambda. *)
  | (cons 0 ?p', fun x : ?T => ?body) => 
      let new_T := simpl_path_r p' T in 
      constr:(fun x : new_T => body)
  | (cons 1 ?p', fun x : ?T => @?body' x) => 
      constr:(fun x : T =>
                 ltac:(let body := beta1 body' x in
                       let r := simpl_path_r p' body in
                       exact r))
  (* Dependent product. *)
  | (cons 0 ?p', forall x : ?T, ?body) => 
      let new_T := simpl_path_r p' T in 
      constr:(forall x : new_T, body)
  | (cons 1 ?p', forall x: ?T, @?body' x) => 
      constr:(forall x : T,
                 ltac:(let body := beta1 body' x in
                       let new_body := simpl_path_r p' body in
                       exact new_body))
  (* Exists. *)
  | (cons 0 ?p', exists x : ?T, ?body) => 
      let new_T := simpl_path_r p' T in 
      constr:(exists x : new_T, body)
  | (cons 1 ?p', exists x: ?T, @?body' x) => 
      constr:(exists x : T,
                 ltac:(let body := beta1 body' x in
                       let new_body := simpl_path_r p' body in
                       exact new_body))
  (* Application. *)
  | (cons 0 ?p', ?f ?x) =>
      let new_f := simpl_path_r p' f in constr:(new_f x)
  | (cons 1 ?p', ?f ?x) =>
      let new_x := simpl_path_r p' x in constr:(f new_x)
  end.
   
(* Simplify the subterm at [path] in the goal. 
   [path] is a list of natural numbers. *)
Ltac simpl_path path :=
  match goal with
  | |- ?g =>
      let g' := simpl_path_r path g in
      change g'
  end.

(* Simplify the subterm at [path] in hypothesis [hyp].
   [path] is a list of natural numbers. *)
Ltac simpl_path_hyp hyp path :=
  let g := type of hyp in
  let g' := simpl_path_r path g in
  change g' in hyp.
  


Ltac beta_head t l :=
    lazymatch t with
    | fun x : ?T => @?body x =>
        match l with
        | cons ?a ?l' =>
            let b := extract a in
          let t' := beta1 body b in
          beta_head t' l'
        end
    | _ =>
        rebuild constr:(cons (mDYN _ t) l)
    end.

Ltac unfold_path_r p t :=
  match p with
  | nil =>
      let l := list_args t in
      match l with
      | cons ?f ?l' =>
          let r := constr:(
                       fun x : unit =>
                         ltac:(
                         let g := extract f in
                         let g' := (eval unfold g in g) in
                         match g' with
                         | _ =>
                             ltac:(
                             is_fix g';
              let r := rebuild constr:(cons (mDYN _ g') l') in
                      let r'' := (eval compute in r) in
                      exact r'')
                         | _ => ltac:(
                                   let r := (  beta_head g' l')
                                   in exact r)
                         end))
                         in beta1 r tt
       end
  | cons ?n ?p' =>
      match t with
      |  forall x: ?T, @?body' x => 
          constr:(forall x : T,
                     ltac:(let body := beta1 body' x in
                           let r := unfold_path_r p' body in
                           exact r))
      |  exists x: ?T, @?body' x => 
          constr:(exists x : T,
                     ltac:(let body := beta1 body' x in
                           let r := unfold_path_r p' body in
                           exact r))
      | fun x : ?T => @?body' x => 
          constr:(fun x : T =>
                     ltac:(let body := beta1 body' x in
                           let r := unfold_path_r p' body in
                           exact r))
      | (?f0 _) =>
          let l := list_args t in
          let u := unfold_path_r
                     p'
                     ltac:(extract ltac:(tnth l (S n))) in
          let l' := ttreplace constr:(mDYN _ u) (S n) l in
          let r := rebuild l'
          in r
      end
  end.

Ltac unfold_path p :=
  match goal with
  | |- ?g =>
      let g' := unfold_path_r p g in
      change g'
  end.

Ltac unfold_path_hyp h p :=
  let g := type of h in
  let g' := unfold_path_r p g in
  change g' in h.

Ltac abst  T t p :=
  let x := fresh "xx" in
  constr:(fun x : T =>
            ltac:( let r := treplace x t p in exact r)).

Ltac vabst v T t p :=
  constr:(fun v : T =>
            ltac:( let r := treplace v t p in exact r)).


Ltac st_aux n l T :=
  let U := eval compute in T in
    let m := eval compute in l in
  lazymatch constr:(m) with
  | cons  (tDYN U) ?y  => constr:(n)
  | cons  _ ?l1  => st_aux constr:(S n) l1 T
  end.

Ltac tst ts T :=
  (st_aux constr:(0) constr:(ts) T). 


(* Definition IDT := fun X:Type => X. *)


Inductive listn :=
  niln | consn : nat -> listn -> listn.
 
Definition test := (cons  (tDYN nat)
                        (cons (tDYN bool)
                              (cons (tDYN Prop)
                   (cons (tDYN listn) nil)))).


 Check (ltac:( let r := 
tst constr:(test) Prop in exact r)).
 

Ltac preify_rec ts p l n env t :=
  let y := fresh "y" in
  let z := fresh "z" in
lazymatch constr:(l) with
  | nil =>
      let t' := find_pat t p in 
      let T :=  type of t' in
      let s := tst ts T in
      let x := fresh "zz" in
      let Q := vabst x T t p in 
      let Q' :=
        constr:(fun y : T =>
                fun z : ppp ts (cons s n) =>
                  ltac:(
                          let b := beta1 Q y in
                          let r :=
                            wrap
                              (cons (mDYN T y) env)
                              z b
                          in exact r)) in
      let Q'' := match Q' with
                 | (fun _ : _ => ?r) => r
                 end
      in
      let obj := constr:(fun z : ppp ts n =>
                           ltac:(let r :=
                                  wrap env z t' in exact r)) in 
     constr:(property ts n s Q'' obj)    
  | cons true ?l' =>
      lazymatch t with
      | ?a -> ?b =>
          let ra := constr:(fun (z: ppp ts n) =>
                              ltac:(let r := wrap env z a
                                    in exact r)) in
          let rb := preify_rec ts p l' n  env b in
          constr:(impr _ n ra rb)
    | ?a /\ ?b => 
          let ra := constr:(fun (z: ppp ts n) =>
                              ltac:(let r := wrap env z a
                                    in exact r)) in
          let rb := preify_rec ts p l' n  env b in
          constr:(andr _ n ra rb) 
    | ?a \/ ?b => 
          let ra := constr:(fun (z: ppp ts n) =>
                              ltac:(let r := wrap env z a
                                    in exact r)) in
          let rb := preify_rec ts p l' n  env b in
          constr:(orr _ n ra rb) 
       end
  | cons false ?l' =>
      lazymatch t with
      | ?a -> ?b =>
          match type of a with
          | Prop =>
               let rb :=
            constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z b
                            in exact r)) in
              let ra := preify_rec ts p l' n  env a in
              constr:(impl _ n ra rb)
          | _ => 
              let y := fresh "y" in
              let s := tst ts a in
              let br :=
                constr:(fun y: a =>
                      ltac:(
                              let s := ltac:(tst ts a) in
                              let r := preify_rec ts p l'
                                             (cons s n)
                                             (cons (mDYN a y) env)
                                             b in
                         exact r))
          in
          match br with
          | (fun _: a => ?r) => constr:(fa ts n (fun y:nat => y)
                                           s
                                           r) 
          end
          end
      | not ?a =>
          let ra := preify_rec ts p l' n  env a in
          constr:(cNot _ n ra)
      | forall x: ?T, @?body' x =>
          let s := tst ts T in
          let y := fresh "y" in
          lazymatch constr:(fun y: T => ltac:(
           let body := beta1 body' y in
           let r := preify_rec ts p l'
                               (cons s n)
                               (cons (mDYN T y) env)
                               body in
              exact r))
     with
     | (fun _: _ => ?r) => constr:(fa ts n s (fun x:nat=>x) r) 
     end 
       | exists x: ?T, @?body' x =>
          let s := tst ts T in
          let y := fresh "y" in
          lazymatch constr:(fun y: T => ltac:(
           let body := beta1 body' y in
           let r := preify_rec ts p l'
                               (cons s n)
                               (cons (mDYN T y) env)
                               body in
              exact r))
     with
     | (fun _: _ => ?r) => constr:(ex ts n s (fun x:nat=>x) r) 
     end 
      | ?a /\ ?b => 
          let rb := constr:(fun (z: ppp ts n) =>
                              ltac:(let r := wrap env z b
                                    in exact r)) in
          let ra := preify_rec ts p l' n  env a in
          constr:(andl _ n ra rb) 
      | ?a \/ ?b => 
          let rb := constr:(fun (z: ppp ts n) =>
                              ltac:(let r := wrap env z b
                                    in exact r)) in
          let ra := preify_rec ts p l' n  env a in
          constr:(orl _ n ra rb) 
     
        | _ => constr:(Hole ts n (fun (z: ppp ts n) =>
                                    ltac:(let r := wrap env z t
                                          in exact r)))
     
      end
end.

Ltac reify_prop ts p l :=
  match goal with
  | |- ?g =>
      let gs := preify_rec ts p l (@nil nat)(@nil DYN) g in
      change (coerce ts (@nil nat) gs tt)
  end.

Ltac reify_prop_hyp ts h h' p l :=
  let gs := preify_rec ts p l
                       (@nil nat)(@nil DYN)
                       ltac:(type of h) in
  have h' : (coerce ts (@nil nat) gs tt) by assumption.

Parameter f : nat -> nat -> nat -> nat.
Parameter R : nat -> nat -> Prop.
(* Check ltac:( let r := 
preify_rec test
                         (cons 0 (cons 1 (cons 2 nil)))(@nil bool)
                         (@nil nat)(@nil DYN)
                          ( (f 0 (f 5 6 7) 2)= 99)
 in exact r).
Set Printing All.
Check 4=4.

   
Goal ( 4 = 3) -> True.
  move => a.

  Check ltac:(let gs := preify_rec test (cons 0 nil) (@nil bool)  (@nil nat)(@nil DYN) ltac:(type of a) in exact gs).
Abort.
Goal (exists x : nat, 3 = 3) -> True.
  move => a.
reify_prop_hyp test a b (@nil nat)(cons false nil).
Abort.

Goal 3=3 /\4=4 -> True.
  move => a.
reify_prop_hyp test a b (@nil nat)(cons false nil).
Abort.
*)

Ltac reify_eq_rec ts' l n env t :=  
  let y := fresh "y" in
  let z := fresh "z" in
  let ts := eval cbn in ts' in
  lazymatch constr:(l) with
  | nil =>
      match t with
      | ?t1 = ?t2 =>
          let T := type of t1 in
          let s := tst ts T in
          let r1 := constr:(fun (z: ppp ts n) =>
                              ltac:(let r := wrap env z t1
                                    in exact r)) in
          let r2 := constr:(fun (z: ppp ts n) =>
                              ltac:(let r := wrap env z t2
                                    in exact r)) in
          constr:(equality ts n s r1 r2)
      end
  | cons true ?l' =>
      lazymatch t with
      | ?a -> ?b => 
          let ra := constr:(fun (z: ppp ts n) =>
                              ltac:(let r := wrap env z a
                                    in exact r)) in
          let rb := reify_eq_rec ts l' n  env b in
          constr:(impr _ n ra rb) 
    | ?a /\ ?b => 
          let ra := constr:(fun (z: ppp ts n) =>
                              ltac:(let r := wrap env z a
                                    in exact r)) in
          let rb := reify_eq_rec ts l' n  env b in
          constr:(andr _ n ra rb) 
    | ?a \/ ?b => 
          let ra := constr:(fun (z: ppp ts n) =>
                              ltac:(let r := wrap env z a
                                    in exact r)) in
          let rb := reify_eq_rec ts l' n  env b in
          constr:(orr _ n ra rb) 
       end
  | cons false ?l' =>
      lazymatch t with
      | not ?a =>
          let ra := reify_eq_rec ts l' n  env a in
          constr:(cNot _ n ra)
       | forall x: (wsort _ ?s), @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: (wsort ts s) => ltac:(
           let body := beta1 body' y in
           let r := reify_eq_rec ts l'
                                 (cons s n)
                                 (cons (mDYN (wsort ts s) y) env)
                                 body in
              exact r))
     with
     | (fun _: (wsort ts s) => ?r) =>
         constr:(fa ts n s (fun x:nat=>x) r) 
     end
      | ?a -> ?b =>
          match type of a with
          | Prop =>       let rb :=
              constr:(fun (z: ppp ts n) =>
                        ltac:(let r := wrap env z b
                              in exact r)) in
            let ra := reify_eq_rec ts l' n  env a in
            constr:(impl _ n ra rb)
          | _ =>
          let s := tst ts a in
                    let y := fresh "y" in
                    lazymatch
                      constr:(fun y: (wsort ts s) =>
                               ltac:(
                                let r := reify_eq_rec ts l'
                                                      (cons s n)
                                                      (cons (mDYN (wsort ts s) y) env) b
                                in
                                exact r))
                    with
                    | (fun _: (wsort ts s) => ?r) =>
                        constr:(fa ts n s (fun y => y) r) 
     end
end
      | ?a -> ?b =>
            let rb :=
              constr:(fun (z: ppp ts n) =>
                        ltac:(let r := wrap env z b in exact r)) in
            let ra := reify_eq_rec ts l' n  env a in
            constr:(impl _ n ra rb)
      | forall x: ?T, @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: T => ltac:(
           let body := beta1 body' y in
           let s := ltac:(tst ts T) in                                  
           let r := reify_eq_rec ts l' (cons s n)
                                 (cons (mDYN T y) env) body in
              exact r))
     with
     | (fun _: T => ?r) => constr:(fa ts n ltac:(let s := tst ts T in exact s) (fun x:nat=>x) r) 
     end
      | exists x: ?T, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: T => ltac:(
          let body := beta1 body' y in
          let s := ltac:(tst ts T) in
       let r := reify_eq_rec ts l' (cons
                               s
                               n) (cons  (mDYN T y) env) body in
       exact r))
     with
     | (fun _: T => ?r) => constr:(ex ts n
                                      ltac:(let s := tst ts T in exact s) (fun x:nat=>x) r)
     end   
      | ?a /\ ?b => 
          let rb := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_eq_rec ts l' n  env a in
          constr:(andl _ n ra rb) 
      | ?a \/ ?b => 
          let rb := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_eq_rec ts l' n  env a in
          constr:(orl _ n ra rb) 
     
        | _ => constr:(Hole ts n (fun (z: ppp ts n) =>
                               ltac:(let r := wrap env z t in exact r)))
     
end
  end.

Ltac reify_eq ts l :=
  match goal with
  | |- ?g =>
      let gs := reify_eq_rec ts l (@nil nat)(@nil DYN) g in
      change (coerce ts (@nil nat) gs tt)
  end.

Ltac reify_eq_hyp ts h h' l :=
  let g := type of h in
  let gs := reify_eq_rec ts l (@nil nat)(@nil DYN) g in
  have h' : (coerce  ts (@nil nat) gs tt) by assumption.

  
Ltac reify_rec ts' l n env t :=
  let y := fresh "y" in
  let z := fresh "z" in
  let ts := eval compute in ts' in
  let c :=  constr:(pair l t) in
  lazymatch c with
  | (nil, _)  => constr:(Hole ts n (fun (z: ppp ts n) =>
                               ltac:(let r := wrap env z t in exact r)))
                          
(*  | (cons 0 ?l', ?a -> ?b) =>
      let rb := constr:(fun (z: ppp ts n) =>
                          ltac:(let r := wrap env z b in exact r)) in
      let ra := reify_rec ts l' n  env a in
      constr:(impl _ n ra rb)  *)
  | (cons 1 ?l', not ?a) =>
          let ra := reify_rec ts l' n  env a in
          constr:(cNot _ n ra)
(*  | (cons 1 ?l', ?a -> False) =>
          let ra := reify_rec ts l' n  env a in
          constr:(cNot _ n ra) *)
  | (cons 1 ?l',  ?a -> ?b) =>
      let ra := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z a in exact r)) in
      let rb := reify_rec ts l' n  env b in
      constr:(impr _ n ra rb)
  |  (cons 1 ?l', ?a /\ ?b) => 
          let ra := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_rec ts l' n  env b in
          constr:(andr _ n ra rb) 
  | (cons 0 (cons 1 ?l'), ?a /\ ?b) => 
          let rb := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_rec ts l' n  env a in
          constr:(andl _ n ra rb) 
  | (cons 1 ?l', ?a \/ ?b) => 
        let ra := constr:(fun (z: ppp ts n) =>
                            ltac:(let r := wrap env z a in exact r)) in
        let rb := reify_rec ts l' n  env b in
        constr:(orr _ n ra rb) 
  | (cons 0 (cons 1 ?l'), ?a \/ ?b) => 
          let rb := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_rec ts l' n  env a in
          constr:(orl _ n ra rb) 
  | (cons 0 ?l', ?a -> ?b) =>
        match type of a with
        | Prop => 
          let rb :=
            constr:(fun (z: ppp ts n) =>
              ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_rec ts l' n  env a in
          constr:(impl _ n ra rb) 
          | _ =>
          let y := fresh "y" in
          lazymatch constr:(fun y: a => ltac:(
           let s := ltac:( tst ts a) in                                  
              let r := reify_rec ts l' (cons s n) (cons (mDYN a y) env) b in
              exact r))
     with
     | (fun _: a => ?r) => constr:(fa ts n ltac:(let s := tst ts a in exact s) (fun x:nat=>x) r) 
     end
     end
  | (cons 1 ?l', forall x: ?T, @?body' x) =>
          let y := fresh "y" in
          lazymatch constr:(fun y: T => ltac:(
           let body := beta1 body' y in
           let s := ltac:( tst ts T) in                                  
              let r := reify_rec ts l' (cons s n) (cons (mDYN T y) env) body in
              exact r))
     with
     | (fun _: T => ?r) => constr:(fa ts n ltac:(let s := tst ts T in exact s) (fun x:nat=>x) r) 
     end
  | (cons 1 ?l', exists x: ?T, @?body' x) =>
     let y := fresh "y" in
     lazymatch constr:(fun y: T => ltac:(
          let body := beta1 body' y in
          let s := ltac:(tst ts T) in
       let r := reify_rec ts l' (cons
                               s
                               n) (cons  (mDYN T y) env) body in
       exact r))
     with
     | (fun _: T => ?r) => constr:(ex ts n
                                      ltac:(let s := tst ts T in exact s) (fun x:nat=>x) r)
     end   
                   
  | _ => constr:(Hole ts n (fun (z: ppp ts n) =>
                               ltac:(let r := wrap env z t in exact r)))
  end.


Ltac reify_goal ts l :=
 lazymatch goal with
 | |- ?g =>
     let r := reify_rec ts l  (@nil nat)  (@nil DYN)  g in
     change (coerce ts (@nil nat) r tt)
 end.

Definition t := forall z x, x = 2 /\ z = true.
Print ls.
Definition cct :=
  ltac:(let r :=
          reify_rec test
                    (cons false (cons false (cons false nil))) (@nil nat)
                    (@nil DYN)
                    (forall z x, x = 2 /\ z = true)  in exact r).

Print cct.


Ltac find_comp l1o l2o :=
  let l1 := eval hnf in l1o in
  let l2 := eval hnf in l2o in
  match l1 with
  | nil => l2
  | cons _ ?l1' =>
      match l2 with
      | cons _ ?l2' =>
          find_comp l1' l2'
      end
  end.

(*
Lemma magic : forall l1 i l2 l3,
    l1 = l2 ++ l3 ->
    wsort l2 i -> wsort l1 i.
elim => [|[T1] l1 hl1][|i][|[T2] l2] l3 /=.
done.
done.
done.
done.
 simpl.
move => [e1 e2].
rewrite e1.
intros _ x; exact x.

intros; apply def.
move => [e1 e2 e3].  
exact (hl1 i l2 l3 e3).
Defined.

Lemma magic_r : forall l1 i l2 l3,
    l1 = l2 ++ l3 ->
    wsort l1 i -> wsort l2 i.
elim => [|[T1 d1] l1 hl1][|i][|[T2 d2] l2] l3.
done.
done.
done.
done.
done.
  simpl.
move => [e1 e2].
rewrite e1.
intros _ x; exact x.

intros; apply def.
move => [e1 e2 e3].  
exact (hl1 i l2 l3 e3).
Defined.


Lemma magic_env :  forall l1 l2 l3,
    l1 = l2 ++ l3 -> wenv l1 -> wenv l2.
move => l1 l2 l3 e; rewrite /env.  
move => f s i.
apply (@magic_r l1 s l2 l3 e).
exact (f s i).
Defined.

Lemma magic_inst2 : forall l1 l2 l3,
    l1 = l2 ++ l3 -> inst2 l2 -> inst2 l1.
move => l1 l2 l3 e [s f].  
exists s.
move => h1 h2.
apply (@magic l1 s l2 l3 e).
apply f.
 exact (magic_env l1 l2 l3 e h1).  
 exact (magic_env l1 l2 l3 e h2).  
Defined.

Definition magic_l : forall l1 l2 l3,
    l1 = l2 ++ l3 -> list (option (inst2 l2)) ->
    list (option (inst2 l1)).
move => l1 l2 l3 e ; elim => [| [d|] l hl].
  apply nil.
apply cons.
exact ( (Some (magic_inst2 l1 l2 l3 e d))).
exact hl.
apply cons.
apply None.
exact hl.
Defined.
  
         
Ltac fetch_def T' l' :=
  let T := eval hnf in T' in
  let l := eval hnf in l' in
    match l with
    | nil =>  constr:(9)
    | cons (mDYN T ?t) _ =>  constr:(t)
    | cons _ ?l'' =>
        fetch_def T l''
  end.

Print test.

Check ltac:(let r := fetch_def Prop constr:(test)
            in exact r).
(* TODO : blinder pour éviter les confusions forall implication *)
 *)


Ltac aDYN T l :=
  let d := constr:(tDYN T) in
  let lh := eval hnf in l in
  match lh with
  | nil => constr:(cons d nil)
  | cons (tDYN T)  _ => l
  | cons ?d' ?l' =>
      let r := aDYN T l' in
      constr:(cons d' r)
  end.




Ltac tp l t := match t with
               | fun XX : ?U =>  forall x : ?T, ?b =>
                   let r := aDYN T l in
                   let nt :=  constr:(fun XX : (forall TT:Type , TT) => (subst! (XX T) for x in b)) in 
                   tp r nt
               | _ => l
               end.

Check ltac:(let r := tp  (@nil TDYN) (fun (XX : forall T, T)=> forall x:nat, x=3) in exact r).

Ltac mkSignR l p t :=
  let c := eval hnf in (p, t) in
    match c with
    | (nil, fun XX : ?U => (@eq ?T _ _)) => aDYN T l
    | (nil, _) => constr:(l)
    | (cons 1 ?p, fun XX : ?U =>  forall x : ?T, ?b) =>
          let r := aDYN T l in
          let nt :=  constr:(fun XX : (forall TT:Type , TT) => (subst! (XX T) for x in b)) in 
          mkSignR r p  nt
    |  (cons 1 ?p, fun XX : ?U =>  exists x : ?T, ?b) =>
          let r := aDYN T l in
          let nt :=  constr:(fun XX : (forall TT:Type , TT) => (subst! (XX T) for x in b)) in 
          mkSignR r p  nt
    |  (cons 1 ?p, fun XX : ?U =>  ?a /\ ?b) =>
          let nt :=  constr:(fun XX : (forall TT:Type , TT) => b) in 
          mkSignR l p  nt
    |  (cons 0 (cons 1 ?p), fun XX : ?U =>  ?a /\ ?b) =>
          let nt :=  constr:(fun XX : (forall TT:Type , TT) => a) in 
          mkSignR l p  nt
    |  (cons 1 ?p, fun XX : ?U =>  ?a \/ ?b) =>
          let nt :=  constr:(fun XX : (forall TT:Type , TT) => b) in 
          mkSignR l p  nt
    |  (cons 0 (cons 1 ?p), fun XX : ?U =>  ?a \/ ?b) =>
          let nt :=  constr:(fun XX : (forall TT:Type , TT) => a) in 
          mkSignR l p  nt
    |  (cons 0 ?p, fun XX : ?U =>  ?a -> ?b) =>
          let nt :=  constr:(fun XX : (forall TT:Type , TT) => a) in 
          mkSignR l p  nt
    |  (cons 1 ?p, fun XX : ?U =>  ?a -> ?b) =>
          let nt :=  constr:(fun XX : (forall TT:Type , TT) => b) in 
          mkSignR l p  nt
      |  (cons 1 ?p, fun XX : ?U => ~ ?a) =>
          let nt :=  constr:(fun XX : (forall TT:Type , TT) => a) in 
          mkSignR l p  nt
  end.


Ltac mkSign p t := mkSignR (@nil TDYN) p (fun XX : (forall TT:Type, TT) => t).

Check ltac:(let r := mkSign (cons 1 (cons 1 nil)) ( forall x, x=3/\true=false) in exact r).


(*

Ltac rmkSign l' c' t' :=
  let l := eval hnf in l' in
  let c := eval hnf in c' in
    let t := eval hnf in t' in 
  match c with
  | impl _ _ ?c' _ =>
      match t with
      |_ -> ?u =>
         rmkSign l c' u
      end
  | orl _ _ ?c' _ =>
      match t with
      |_ \/ ?u =>
         rmkSign l c' u
      end
  | andl _ _ ?c' _ =>
      match t with
      |_ /\ ?u =>
         rmkSign l c' u
      end
  | impr _ _ _ ?c' =>
      match t with
      |?u -> _ =>
         rmkSign l c' u
      end
  | orr _ _ _ ?c' =>
      match t with
      |?u \/ _ =>
         rmkSign l c' u
      end
  | andr _ _ _ ?c' =>
      match t with
      |?u /\ _ =>
         rmkSign l c' u
      end
  | cNot _ _ ?c' =>
      match t with
      | ~ ?u =>
          rmkSign l c' u
      end
  | fa _ _ _ _ ?b =>
      match t with
      | forall x : ?T, ?body =>
          let l' := aDYN T constr:(l) in
          let d := fetch_def T l' in
          rmkSign l' b (subst! d for x in body)
      end
  | ex _ _ _ _ ?b =>
      match t with
      | exists x : ?T, ?body =>
          let l' := aDYN T constr:(l) in
          let d := fetch_def T l' in
           rmkSign l' b (subst! d for x in body)
      end
  | property _ _ _ _ ?t =>
      let T := type of t in
      aDYN T constr:(l)
  | equality _ _ _ ?t1 _ =>
      let T1 := type of t1 in
      let PT1 := eval hnf in T1 in
        match PT1 with
        | prod ?T _ => aDYN T constr:(l)
        end
  | _ => l
  end.

*)

(* same but detecting True and False *)

Ltac reify_rec_at ts' l n env t := 
  let z := fresh "z" in
  let ts := eval cbn in ts' in
  let c :=  (pair  l t) in
  lazymatch c with
  | (nil, True) => constr:(cTop ts n)
  | (nil, False) => constr:(cBot ts n)
  | (nil, _) =>
          constr:(Hole ts n (fun (z: ppp ts n) =>
                            ltac:(let r0 := wrap env z t in exact r0)))
   | (cons 1 ?l',  ~ ?a) =>
           let ra := reify_rec_at ts l' n  env a in
          constr:(cNot _ n ra)
  | (cons 1 ?l', ?a -> False) =>
           let ra := reify_rec_at ts l' n  env a in
          constr:(cNot _ n ra)


 | (cons 1 ?l', ?a -> ?b) => 
      let ra := constr:(fun (z: ppp ts n) =>
                          ltac:(let r := wrap env z a in exact r))
      in
      let rb := reify_rec_at ts l' n  env b in
      constr:(impr _ n ra rb)
  | (cons 0  ?l', ?a -> ?b) =>
      match type of a with
      | Prop =>
          let rb := constr:(fun (z: ppp ts n) =>
                              ltac:(let r := wrap env z b in exact r))
          in
          let ra := reify_rec_at ts l' n  env a in
          constr:(impl _ n ra rb) 
      | _ => 
       let y := fresh "y" in
       lazymatch constr:(fun y: a => ltac:(
              let s := ltac:(tst ts a)
              in                                  
              let r := reify_rec_at ts l' (cons s n) (cons (mDYN a y) env) b in
           exact r))
       with
       | (fun _: a => ?r) => constr:(fa ts n ltac:(let s := tst ts a in exact s) r) 
       end
      end 
  
  | ((cons 1 ?l'), ?a /\ ?b) => 
      let ra := constr:(fun (z: ppp ts n) =>
                          ltac:(let r := wrap env z a in exact r))
      in
      let rb := reify_rec_at ts l' n  env b in
          constr:(andr _ n ra rb) 
  |  ((cons 1 ?l'), (or ?a ?b)) => fail;
         let ra := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_rec_at ts l' n  env b in
          constr:(orr _ n ra rb)
  | (cons 0 (cons 1 ?l'), ?a /\ ?b) => 
          let rb := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_rec_at ts l' n  env a in
          constr:(andl _ n ra rb) 
  |  (cons 0 (cons 1 ?l'), ?a \/ ?b) => 
          let rb := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_rec_at l' n  env a in
          constr:(orl _ n ra rb)  

  | (cons 1 ?l', forall x: (wsort _ ?s), @?body' x) =>
          let y := fresh "y" in
          lazymatch constr:(fun y: (wsort s) => ltac:(
           let body := beta1 body' y in
              let r := reify_rec_at ts l' (cons s n) (cons (mDYN (wsort ts s) y) env) body in
              exact r))
     with
     | (fun _: (wsort ts s) => ?r) => constr:(fa ts n s r) 
     end
  |  (cons 1 ?l',forall x: ?T, @?body' x) =>
          let y := fresh "y" in
          lazymatch constr:(fun y: T => ltac:(
           let body := beta1 body' y in
           let s := ltac:(tst ts T) in                                  
              let r := reify_rec_at ts l' (cons s n) (cons (mDYN T y) env) body in
              exact r))
     with
     | (fun _: T => ?r) => constr:(fa ts n ltac:(let s := tst ts T in exact s) r) 
     end
  | (cons 1 ?l', exists x: ?T, @?body' x) =>
     let y := fresh "y" in
     lazymatch constr:(fun y: T => ltac:(
          let body := beta1 body' y in
           let s := ltac:(tst ts T) in                         let r := reify_rec_at ts l' (cons
                               s
                               n) (cons  (mDYN T y) env) body in
       exact r))
     with
     | (fun _: T => ?r) => constr:(ex ts n
                                      ltac:(let s := tst ts T in exact s)
                                             r)
     end        
  | _ => constr:(Hole ts n (fun (z: ppp ts n) =>
                               ltac:(let r := wrap env z t in exact r))) 
     
  end.


Ltac reify_goal_at ts l :=
 lazymatch goal with
 | |- ?g =>
     let g' := eval hnf in g in
       let r1 := reify_rec_at ts l (@nil nat)  (@nil DYN) g'
       in change (coerce ts (@nil nat) r1 tt)
 end.

Ltac reify_hyp ts l h :=
 let o := type of h in
 match o with
 | ?g =>
     let r := reify_rec ts l (@nil nat)  (@nil DYN) g in (change (coerce ts (@nil nat) r tt) in h)
 end.

Ltac reify_hyp_at ts l h :=
 let o := type of h in
 match o with
 | ?g =>
     let r := reify_rec_at ts l (@nil nat)  (@nil DYN) g in (change (coerce ts (@nil nat) r tt) in h)
 end.

(* l : path to instantiation (go below instantiated quantifier
   h : name of instantiated hypothesis
   h' : name of resulting hypothesis
   s : number of instantiated sort
   o : instantiating object (of type (sort s) *)

Ltac inst_hyp ts l h h' s o :=
  let x := fresh "x" in
  move: (h) => x;
               reify_hyp ts l x;
  let sy := type of x in
   match sy with
   | coerce _ (@nil nat) ?hc _ =>
       move: (instp_corr ts  (pred (length l))  s o (@nil nat) hc tt h) => h';
       rewrite /= (* ?trs_corr *) in h';
       rewrite  /eqnqtdec /eq_rect_r /eq_rect /eq_ind_r /eq_ind /nat_rec /eq_sym  /nat_rect /wsort in h';
       clear x
   end;
   try discriminate.



Ltac dyn_inst_hyp l h h' o :=
  let ht := type of h in
  let ts := mkSign l ht in
  let to := type of o in
  let s := tst ts to in
  inst_hyp ts l h h' s o.

(*
Goal  (forall x y, x = true -> y = 4) -> False.
  intro h.

reify_hyp (cons (tDYN nat) nil)  (cons 1 (@nil nat)) h.
  
  ltac:(dyn_inst_hyp (cons 1 (cons 1 nil))  h h' 8).
Abort.
*)
  
Ltac inst_hyp_nd ts l h s o :=
  reify_hyp ts l h;
  let sy := type of h in
   match sy with
   | coerce _ (@nil nat) ?hc _ => 
       move: (instp_corr ts (pred (length l))  s o (@nil nat) hc tt h);
       clear h; move => h;
       rewrite /=  in h;
        rewrite  /eqnqtdec  /eq_ind_r /eq_ind  /eq_rect_r /eq_rect /nat_rec /eq_sym  /nat_rect /wsort /sl  in h
   end;
   try discriminate.


Ltac dyn_inst_hyp_nd l h o :=
    let ht := type of h in
  let ts := mkSign l ht in
  let to := type of o in
  let s := tst ts to in
  inst_hyp_nd ts l h s o.

(*  
Check ltac:(let r := tst [:: tDYN Prop] Prop in exact r).
   Goal (forall X :  Prop,  X) -> False.
intro h.
dyn_inst_hyp_nd  (cons 1 nil) h False.
by apply h.
Abort. 
*)



Ltac inst_goal ts l o :=
  reify_goal ts l;
  let ho := type of o in
  let s := tst ts ho in 
  match goal with
  | |- coerce _ (@nil nat) ?hc _ => 
       apply (instn_corr ts (pred (length l))  s o (@nil nat) hc tt);
       rewrite /=  /instn /eqnqtdec  /eq_ind_r /eq_ind  /eq_rect_r /eq_rect /nat_rec /eq_sym  /nat_rect /wsort /sl
   end;
  try discriminate.

Ltac dyn_inst_goal l o :=
     match goal with
     | |- ?g => 
         let ts := mkSign l g in 
        inst_goal ts l o
     end.
(*
Goal exists x:nat, exists y, x = (S y).
  dyn_inst_goal (cons false (cons false nil)) 4.  
Abort.
*)


(*
Ltac inst_goal ts' l s o :=
  let ts'' := tmDYN ts' in
  match goal with
  | |- ?g =>
      let ts := mkSign ts'' l g in
      inst_goal_o ts l s o
  end.
*)
(* Once a back or forward steps is performed, we want to apply simplification
   (simpl function).
  For that we need to translate the o3 back into a cx *)
(*
(* this finds the path to the focused location *)
Ltac find_path p :=
  lazymatch p with
  | Hol3 _ => constr:(@nil bool)
  | not3 ?q => let rq :=(find_path q) in constr:(cons false rq)
  | impl3 ?q _ =>  let rq :=(find_path q) in constr:(cons false rq)
  | impr3 _ ?q => let rq := (find_path q) in constr:(cons true rq)
  | orl3 ?q _ => let rq := (find_path q) in constr:(cons false rq)
  | orr3 _ ?q => let rq := (find_path q) in constr:(cons true rq)
  | andl3 ?q _ => let rq := (find_path q) in constr:(cons false rq)
  | andr3 _ ?q => let rq := (find_path q) in constr:(cons true rq)
  | fa3 ?s ?f =>
      let ff := eval compute in
      (f (def s)) in
      let rq := (find_path ff) in constr:(cons false rq)
  | ex3 ?s ?f =>
      let ff:= eval compute in (f (def s)) in
        let rq := (find_path ff) in constr:(cons false rq)
  | _ => constr:(@nil bool)
  end.

(* to go from o3 to cx in order to perform the simplification *)
Ltac rereify_goal ts :=
  match goal with
  | |- (trl3 ?o) =>
      let r := (find_path constr:(o)) in
      rewrite /trl3 /=; reify_goal_at ts r
  end.

Ltac rereify_hyp ts h :=
  let oo := type of h in
  match oo with
  | trl3 ?o =>
        let r := (find_path constr:(o)) in
      rewrite /trl3 /= in h; reify_hyp_at ts r h
  end.
*)


      
Ltac myhnf t :=
  match t with
  | tr3 _ _ =>
  let t0 := eval hnf in t in
    match t0 with
    | ?A \/ ?B =>
        let rA := myhnf A in
        let rB := myhnf B in
        constr:(rA \/ rB)
    | ?A /\ ?B =>
        let rA := myhnf A in
        let rB := myhnf B in
        constr:(rA /\ rB)
    | ?A -> ?B =>
        let rA := myhnf A in
        let rB := myhnf B in
        constr:(rA -> rB)
    | forall x : ?T, ?B =>
        let y := fresh x in
        let T' := eval simpl in T in
          constr:(forall y : T',
                     let B' := (subst! y for x in B) in
             ltac:(let r := myhnf B' in exact r))
    | exists x : ?T, ?B =>
        let y := fresh x in
        let T' := eval simpl in T in
          constr:(exists y : T',
                     let B' := (subst! y for x in B) in
                     ltac:(let r := myhnf B in exact r))
    | ~ ?A => let rA := myhnf A in
              constr:(~ rA)
    | ?X => constr:(X)
    end
  | _ => t
  end.

(*
                constr:(orr3 h r)
    | orl3  ?u ?h =>
        let r := myhnf u in
        constr:(orl3 r h)
    | andr3 ?h ?u =>
        let r := myhnf u in
        constr:(andr3 h r)
    | andl3 ?u ?h =>
        let r := myhnf u in
        constr:(andl3 r h)
    | impr3 ?h ?u =>
        let r := myhnf u in
        constr:(impr3 h r)
    | impl3 ?u ?h =>
        let r := myhnf u in
        constr:(impl3 r h)
    | fa3 ?s ?f =>
        constr:(fa3 s (fun x =>
                 ltac:(let body := beta1 f x in
                       let r := myhnf body in
                       exact r)))
    | ex3 ?s ?f =>
        constr:(ex3 s (fun x =>
                 ltac:(let body := beta1 f x in
                       let r := myhnf body in
                       exact r)))
    | not3 ?u =>
        let r := myhnf u in
       constr:(not3 r)
    | ?X => X
    end. *)

Ltac myhnf_goal :=
  rewrite /o3_norm;
  match goal with
  | |- trl3 ?m ?o =>
      let r := myhnf (tr3 m o) in
      change r
  end.

Ltac myhnf_hyp h :=
  rewrite /o3_norm in h;
  match type of h with
  | trl3 ?m ?o =>
      let r := myhnf (tr3 m o) in
      change r in h
  end.

(* builds the list of types of A1 -> A2 ->  ... An ->  unit  *)
Ltac reify_uncurryR ts l T :=
  match T with
  | (?A -> ?B) =>
      let nA := tst ts A in
         reify_uncurryR ts constr:(cons nA l) B 
  | ?U => l
  end.

Definition ts := (cons (tDYN Prop) (cons (tDYN nat) (cons (tDYN bool) nil))).

Check ( nat -> nat -> bool -> nat).
Check ltac:(let r := reify_uncurryR ts (@nil nat) ( nat -> nat -> bool -> nat) in exact r).

(* transforms  A1 * A2 *  ... An *  unit -> B  into 
   [An; ... ; A2; A1] , B             *)
Ltac reify_result ts T :=
  match T with
  | ?A -> ?B => reify_result ts B
  | ?U => tst ts U
  end.

Ltac reify_uncurry ts T :=
  let r := reify_result ts T in
  let args := reify_uncurryR ts constr:(@nil nat) T in
  constr:((args, r)).

(* only for tests ? *)
Ltac reify_curryR ts l T :=
  match T with
  | (?B -> ?A) =>
      let nB := tst ts B in
         reify_curryR ts constr:(cons nB l) A 
  | ?U => let tU := tst ts U in
          constr:((l, tU))
  end.
Check insti.
Print ty_curry.


Ltac remove f :=
  match f with
  |(fun x : _ => ?body) => body
  | _ => constr:(8)
  end.

Ltac nremove f n :=
  match n with
  | 0 => f
  | S ?m =>
      let f' := remove f in
      nremove f' m
  end.

Ltac remove1 f :=
  match f with
  |(fun (x : ?X)(y : _) => ?body) => constr:(fun (x:X) => body)
  end.

Ltac remove2 f :=
  match f with
  |(fun (x : ?X)(y : ?Y)(z:_) => ?body) =>
     constr:(fun (x:X)(y:Y) => body)
  | _ => constr:(19)
  end.

Ltac nremove1 f n :=
  match n with
  | 0 => f
  | S ?m =>
      let f' := remove1 f in
      let f'' :=  nremove1 f' m in f''
  end.


Ltac nremove2 f n :=
  match n with
  | 0 => f
  | S ?m =>
      let f' := remove2 f in
      nremove f' m
  end.

Ltac invert f :=
  match f with
  | (fun (x1 : ?T1)(x2 : ?T2)(x3 : ?T3)(x4 : ?T4)
         (x5 : ?T5)(x6 : ?T6) (x7 : ?T7)(x8 : ?T8)
     (x9 : ?T9)(x0 : ?T0) =>
       ?body) =>
      constr:(fun (x0:T0)(x9:T9)(x8:T8)(x7:T7)(x6:T6)
                  (x5:T5)(x4:T4)(x3:T3)(x2:T2)(x1:T1) =>
                body)
  | (fun (x1 : ?T1)(x2 : ?T2)(x3 : ?T3)(x4 : ?T4)
         (x5 : ?T5)(x6 : ?T6) (x7 : ?T7)(x8 : ?T8)
     (x9 : ?T9) =>
       ?body) =>
      constr:(fun (x9:T9)(x8:T8)(x7:T7)(x6:T6)
                  (x5:T5)(x4:T4)(x3:T3)(x2:T2)(x1:T1) =>
                body)
  | (fun (x1 : ?T1)(x2 : ?T2)(x3 : ?T3)(x4 : ?T4)
         (x5 : ?T5)(x6 : ?T6) (x7 : ?T7)(x8 : ?T8)=>
       ?body) =>
      constr:(fun (x8:T8)(x7:T7)(x6:T6)
                  (x5:T5)(x4:T4)(x3:T3)(x2:T2)(x1:T1) =>
                body)
  | (fun (x1 : ?T1)(x2 : ?T2)(x3 : ?T3)(x4 : ?T4)
         (x5 : ?T5)(x6 : ?T6) (x7 : ?T7)=>
       ?body) =>
      constr:(fun (x7:T7)(x6:T6)
                  (x5:T5)(x4:T4)(x3:T3)(x2:T2)(x1:T1) =>
                body)
  | (fun (x1 : ?T1)(x2 : ?T2)(x3 : ?T3)(x4 : ?T4)
         (x5 : ?T5)(x6 : ?T6) =>
       ?body) =>
      constr:(fun (x6:T6)
                  (x5:T5)(x4:T4)(x3:T3)(x2:T2)(x1:T1) =>
                body)
  | (fun (x1 : ?T1)(x2 : ?T2)(x3 : ?T3)(x4 : ?T4)(x5 : ?T5) =>
       ?body) =>
      constr:(fun (x5:T5)(x4:T4)(x3:T3)(x2:T2)(x1:T1) =>
                body)
  | (fun (x1 : ?T1)(x2 : ?T2)(x3 : ?T3)(x4 : ?T4) =>
       ?body) =>
      constr:(fun (x4 : T4)(x3 : T3)(x2 : T2)(x1 : T1) =>
                body)
  | (fun (x1 : ?T1)(x2 : ?T2)(x3 : ?T3) => ?body) =>
      constr:(fun (x3 : T3)(x2 : T2)(x1 : T1) => body)
  | (fun (x1 : ?T1)(x2 : ?T2) => ?body) =>
      constr:(fun (x2 : T2)(x1 : T1) => body)
  | ?f => f
end.


Ltac truncate f n :=
  let f' := invert f in
  let g := nremove f' n in
  invert g.

Ltac c1 f :=
  let g :=
  match f with
  | (fun x : (?A * ?B)%type => ?body) =>
      constr:(fun (x1:A) (x2:B) => (subst! (x1, x2) for x in body))
  end
  in
  eval hnf in g.
Check (fun c =>
                    match c with (x,y) => x + y end).
Check ltac:(let r :=
              c1 (fun c =>
                    match c with (x,y) => x + y end)
                 in exact r).


Ltac c2 f :=
  let g :=
    match f with
    | (fun (x:?A)(y:?B) => ?body) =>
        constr:(fun (c : A * B) =>
          (subst!  let (x',y') := c in x' for x in (subst!  let (x',y') := c in y' for y in body)))
    end
  in
  eval hnf in g.

Ltac c3 f :=
  let g :=
    match f with
    | (fun (x:?A)(y:?B)(z:?C) => ?body) =>
        constr:(fun (x:A)(c : B * C) =>
                  (subst!  let (y',z') := c in y' for y in
                             (subst!  let (y',z') := c in z' for z in
                                        body)))
    end
  in
  eval hnf in g.


Ltac decurryn_a f n :=
  match constr:(n) with
  | 0 => f
  | S ?n' =>
      let g := c2 f in
      decurryn_a g n'
  end.

Ltac decurryn f n :=
  let g := constr:(fun (_ : unit) => f) in
  decurryn_a g n.

Check ltac:(let r := decurryn
                       (fun a b c x y : nat => a+b+c+x+y)
                       3
                       in exact r).

Ltac decurryn_ad f n :=
  match constr:(n) with
  | 0 => f
  | S ?n' =>
      let g := c3 f in
      decurryn_ad g n'
  end.

Ltac decurryn_d f n :=
  let nf :=
    match f with
    | (fun (c : ?C) => ?body) =>
        constr:(fun (c:C)(_ : unit) => body)
    end
  in
  decurryn_ad nf n.

Check ltac:(let r := decurryn
                       (fun a b c x y : nat => a+b+c+x+y)
                       3
            in
            let r1 := decurryn_d r 2 in
            exact r1).

Ltac get_sign ts T :=
  match T with
  | ?A -> ?U =>
      let r := get_sign ts U in
      let nA := tst ts A in
      constr:(cons nA r)
  | _ => constr:(@nil nat)
  end.

Ltac get_result ts T :=
  match T with
  | _ -> ?U => get_result ts U
  | _ => tst ts T
  end.

Ltac dress ts l :=
  match l with
  | nil => constr:(@nil (option (inst1 ts)))
  | cons None ?l' =>
      let r := dress ts l' in
      constr:(cons (@None (inst1 ts)) r)
  | cons (Some (mDYN _ ?f)) ?l' =>
      let T := type of f in
      let r := dress ts l' in 
      let s := get_sign ts T in
      let sr := get_result ts T in  
      constr:(cons (Some (@insti ts sr s f)) r) 
  end.

Check ltac:(let r :=
              dress (cons (tDYN nat) nil)
                    (Some (mDYN (nat -> nat) (fun x : nat => x))
:: nil)%list
in exact r).

     
Ltac back_o ts'  h0 hp gp t i :=
  let ts := fresh "ts" in
  pose ts := ts';
  let h := fresh "h" in
  move: (h0) => h;
  reify_goal ts gp;
  reify_hyp ts hp h;
  let o := type of h in
  match o with
  | coerce _ (@nil nat) ?hc _ => 
      let i' := dress ts i in
      apply (b3_corr ts false t false i'
                     (@nil nat) tt (@nil nat) tt hc);
      [idtac|assumption];
      (apply trex_norm_apply;
       [simpl; try done; auto|
         rewrite ?/ts /b3 /o3_norm /coerce ; 
         try exact tt]
        )  end;
         let sq :=
           match goal with
           | |- trl3 _ ?o => o
           | |- ?xx => xx
           end
         in clear h;
     rewrite   /b3 /o3_norm /trl3  /coerce /xor 
                   /tr3  /check_curry  /check_list /eq_list /list_rec /eq_rect_r /eq_rect /eq_sym /seq.cat /check_nat /eq_nat /eqnqtdec  /app_curry /nat_rec /nat_rect /eq_rect_r /eq_rect
                   /eq_ind_r /eq_ind  /eq_sym /list_rect /eq_rect_r /eq_rect /eq_sym /ppconcat
                   /ts  /wsort /sl;
                simplify_goal;
         let tg :=
           match goal with
           | |- ?tt => tt
           end
         in
         let nt := orename sq tg
         in (try change nt);
         simplify_goal;
        (try by apply I);
            (try discriminate);
            try clear ts. 

Ltac revinsti t :=
  let h := eval compute in t in
  match constr:(h) with
  | cons (Some (mDYN _ ?f)) _  => f
  | _ => constr:(3)
  end.

  Ltac check t :=
    match t with
    | (insti _ _ _ _) => constr:(1)
    | (cons (Some (insti _ _ _ _ ))  _ ) => constr:(2)
    | (cons (Some (mDYN _ _ ))  _ ) => constr:(7)
    | (cons (Some ?e)  _ ) => constr:(e)
    | (cons None   _ ) => constr:(4)
    | (cons (Some _)  _ ) => constr:(6)
    | (cons _  _ ) => constr:(5)
    | (mDYN _ _ ) => constr:(3)
    | _ => 5
    end.

Ltac depiot i :=
  match i with
  | cons (Some (mDYN _ ?f)) ?i' =>   generalize (refl_equal 3) ;
                                     generalize (refl_equal f)
  | cons (Some ?f) ?i' =>
      generalize (refl_equal f)
  | cons _ i =>  depiot i (* generalize (refl_equal 7) *)
  | nil  => generalize (refl_equal 8)
  | _  => generalize (refl_equal i)
  end.

      
(*

Ltac back h hp gp t i :=
       let rr := check i in
      cut (rr = rr).
 *)

                                

  
Ltac clean l :=
  match l with
  | nil  => l
  | cons (mDYN _ ?t) ?l' =>
      let lr := clean l' in
      let tot := type of t in
       constr:(cons (mDYN tot t) lr)
  end.

Ltac back h hp gp t i :=
 (* generalize (refl_equal i). *)
  let th := type of h in
  let ts1 := mkSign hp th in 
  match goal with
  | |- ?tg =>
      let ts :=
        mkSignR ts1 gp (fun XX : (forall TT:Type, TT) => tg) in
      let ts' := eval hnf in ts in
      back_o ts' h hp gp t i
  end. 

(*  let th := type of h0 in
  let ts'' := mkSign ts''' hp th in 
  match goal with
  | |- ?g =>
      let ts := mkSign ts'' gp g in
      back_o ts' h0 hp gp t i
  end. *)



Parameter A B: Prop.

(*
Lemma x1 : A -> A.
intros H.

back H (@nil bool)(@nil bool) (@nil bool) (@nil nat).
Qed. *)
(*
Goal A -> A/\B.
  intro a.
  back
       a (@nil bool)(cons false  nil)(cons true ( nil))
       (@nil bool).  
Abort.
Print inst1.

*)


Ltac reify_funtypeR ts l T :=
  match T with
  | ?A -> ?B => let na := tst ts A in
                reify_funtypeR ts constr:(cons na l) B
  | _ => let nU := tst ts T in
          constr:((l, nU))
  end.

Ltac reify_funtype ts T :=
  reify_funtypeR ts constr:(@nil nat) T.

(* 
Check ltac:(let r :=  dress ts (cons (mDYN _ fff) nil) in
            exact r).
           
Check ltac:(let r := reify_funtypeR ts (@nil nat) (nat->nat->bool) in exact r).
Check ltac:(let r := reify_funtype ts  (nat->nat->bool) in exact r).


Goal exists f : nat -> nat -> nat, forall x y, f y ( x) = (2+y+x).
eapply (ex_intro _ (fun x y =>  _)).
intros x y. reflexivity.
Save titi.  
Print titi. *)


(* rewrite with hypothesis h in goal 
 hp : list bool = path to the equality
 gp : list bool = path to the atomic proposition containing the term
 gp' : list nat = path to the term
 t : list bool = trace (with the last bool for choice l <-> r)
 i : instantiation *)

Ltac rew_dnd_o ts' h hp gp gp' t i :=
  let tsc := eval compute in ts' in
  let ts := fresh "ts" in
  pose ts := tsc; 
  let fl := get_last t in
  let t' := snitch_last t in
  reify_prop ts gp gp'; 
  let h' := fresh "h" in
  reify_eq_hyp ts h h' hp;
  let ec :=
    match type of h' with
    | coerce _ _ ?e _ => e
    end in 
 let gc :=
    match goal with
    | |- coerce _ _ ?g _  => g
    end in
    let ni := eval compute in
               (bc3 ts 0 0 false t i
                                nil
                                false nil ec nil gc) in
             match ni with
             | (?l, ?ah, ?ag) =>
                  let l' := eval compute in (List.rev l) in
                  let i' := dress ts l' ah ag in
  apply (b3_corr ts fl t' false i'  (@nil nat) tt (@nil nat) tt
                 ec gc)
        end;
  [idtac| assumption];
  (apply trex_norm_apply ; [split; try reflexivity|idtac]);
  (try clear h');
  let os :=
    match goal with
    | |- trl3 _ ?o => o
    end
  in
  rewrite   /b3 /trl3 /o3_norm /coerce  /xor /tr3  /eq_nat /check_nat /eqnqtdec
            /nat_rec /nat_rect  /list_rect /eq_rect_r /eq_rect /eq_sym /f_equal
            /eq_ind_r /eq_ind  /eq_sym /ts;
  match goal with
  | |- ?tt =>
      let nt := orename os tt in
      try
        change nt
  end;
    simplify_goal;
  rewrite  /wsort /sl; try clear ts.



(* rewrite in hypothesis h using an equality in the goal 
 hp : list bool = path to the atomic prop in the hyp
 hp' : list bool = path to the term
 gp : list nat = path to the equality
 t : list bool = trace (with the last bool for choice l <-> r)
 i : instantiation *)


Ltac rew_dnd_rev_o ts' h hp hp' gp t i :=
  let fl := get_last t in
  let t' := snitch_last t in
  let tsc := eval compute in ts' in
  let ts := fresh "ts" in
  pose ts := tsc;
  reify_eq ts gp;
  let h' := fresh "h" in 
  reify_prop_hyp ts h h' hp hp';
  let ec :=
    match type of h' with
    | coerce _ _ ?e _ => e
    end in 
 let gc :=
    match goal with
    | |- coerce _ _ ?g _  => g
    end in 
    let ni := eval compute in
               (bc3 ts 0 0 false t i
                                nil
                                false nil ec nil gc) in
      match ni with
      | (?l, ?ah, ?ag) =>
          let l' := eval compute in (List.rev l) in
            let i' := dress ts l' ah ag in
    apply (b3_corr ts fl t' false i' (@nil nat) tt (@nil nat) tt
                   ec gc)
    end;
  [idtac| assumption];
  (apply trex_norm_apply ; [split; try reflexivity|idtac]);
  try clear h';
  try(
  let os :=
    match goal with
    | |- trl3 _ ?o => o
    end
  in
  rewrite   /b3 /trl3 /o3_norm /coerce  /xor /tr3  /eq_nat /check_nat /eqnqtdec
            /nat_rec /nat_rect  /list_rect /eq_rect_r /eq_rect /eq_sym /f_equal
            /eq_ind_r /eq_ind  /eq_sym /ts;
  match goal with
  | |- ?tt =>
      let nt := orename os tt in
      try
        change nt
  end);
    simplify_goal;
  rewrite  /wsort /sl; try clear ts.


Ltac rew_dnd_rev  h hp hp' gp t i :=
  let ht := type of h in
  let ts1 := mkSign hp' ht in 
  match goal with
  | |- ?gt =>
      let ts := mkSignR ts1 gp  (fun XX : (forall TT:Type, TT) => gt) in
      rew_dnd_rev_o ts h hp hp' gp t i
  end.

Ltac rew_dnd  h hp gp gp' t i :=
  let th := type of h in
  let ts1 := mkSign hp th in 
  match goal with
  | |- ?gt =>
      let ts := mkSignR ts1 gp'  (fun XX : (forall TT:Type, TT) => gt) in
      idtac "c2";
      rew_dnd_o ts h hp gp gp' t i
  end.




(*

    let ts''' := eval hnf in ts' in
   let th := type of h in
  let ts'' := mkSign ts''' hp th in 
  let e := fresh "e" in
  match goal with
  | |- ?g =>
      let ts := mkSign ts'' gp' g in
  (*    let diff := find_comp ts''' ts in
      let e := constr:(refl_equal ts) in 
      let i' := constr:(magic_l ts ts''' diff e i) in
      let i'' := eval hnf in i' in
      let i''' := eval simpl in i'' in *)
        let tsw := tmDYN ts 
        let iw := constr:(restrip tsw i') in
      rew_dnd_o tsw h hp gp gp' t iw
  end. *)
  
(*
Definition iin  : nat -> list (option inst2).
  intro n.
apply cons; last apply nil.
apply Some; exists 0.
move => *; exact n.
Defined.

Parameter P : nat -> Prop.
Goal P 0 -> 0=2 -> P 2.
intro h.
rew_dnd' h (@nil bool)(cons 0 nil)
         (cons false nil)
         (cons true (cons true nil)) (@nil (option inst2)).
Abort.



Goal P 0 -> 2=0 -> P 2.
intro h.
rew_dnd' h (@nil bool)(cons 0 nil)
         (cons false nil)
         (cons true (cons false nil)) (@nil (option inst2)).
Abort.
*)



(* rewrite with hypothesis h1 in hyp h2 to yield new hyp h3 
 hp1 : list bool = path to the equality
 hp2 : list bool = path to the atomic proposition containing the term
 hp2' : list nat = path to the term
 t : list bool = trace (with the last bool for choice l <-> r)
 i : instantiation *)

Fixpoint inv_trace l :=
  match l with
  | cons true l' => cons false (inv_trace l')
  | cons false l' => cons true (inv_trace l')
  | x => x
  end.

Fixpoint is_eq o1 o2 (t: cx o1 o2) : bool :=
  match t with
  | equality _ _ _ _ => true
  | fa _ _ _ t' => is_eq _ _ t'
  | ex _ _ _ t' => is_eq _ _ t'
  | impr _ _ t' => is_eq _ _ t'
  | orr _ _ t' => is_eq _ _ t'
  | andr _ _ t' => is_eq _ _ t'
  | impl _ t' _ => is_eq _ _ t'
  | orl _ t' _ => is_eq _ _ t'
  | andl _ t' _ => is_eq _ _ t'
  | _ => false
  end.

Ltac lpl l :=
  match l with
  | cons true ?l' =>  idtac "t = true"; lpl l'
  | cons false ?l' =>  idtac "t = false"; lpl l'
  | _ => idtac
  end.

Ltac rew_dnd_hyp_o ts' fl  h1 h2 h3 hp1 hp2 hp2' t i :=
(*  lpl t; *)
  let flt := get_last t in
  let t' := snitch_last t in
  let tsc := eval compute in ts' in
  let ts := fresh "t" in 
  let i' := eval compute in i in
  let h1' := fresh "h1" in
  let h2' := fresh "h2" in
  let h4 := fresh "h4" in
  let h5 := fresh "h5" in
  pose ts:= tsc;
  reify_eq_hyp ts h1 h1' hp1;
  reify_prop_hyp ts h2 h2' hp2' hp2;
  let hc1 :=
    match type of h1' with
    | coerce _ (@nil nat) ?hc1 _ => hc1
    end
  in
  let hc2 :=
    match type of h2' with
    | coerce _ (@nil nat) ?hc2 _  => hc2
    end in
  clear h1' h2';
  let nfl := eval hnf in (negb fl) in  (* maybe do a switch_inst *)
  let ni := eval compute in
               (fc3 ts 0 0 false t i
                                nil
                                false nil hc1 nil hc2) in
             match ni with
             | (?l, ?ah, ?ag) =>
                  let l' := eval compute in (List.rev l) in
                  let i' := dress ts l' ah ag in
      move:
        (f3_corr ts flt t' nfl
                       i' (@nil nat) hc2 tt
                       (@nil nat) hc1 tt h2 h1) => h4
             end;
  let oh4 :=
    match type of h4 with
    | (trl3 _ ?oh) => oh
    end in
  cut (trex ts oh4); [idtac| by split];
  move => h5;
  move: (trex_norm_fapply ts oh4 h5 h4) => h3;
  try (clear h5); try (clear h4);
  let st :=
    match type of h3 with
    | trl3 _ ?oh => oh
    end in
  rewrite   /f3 /trl3 /o3_norm /coerce  /xor /tr3  /eq_nat /check_nat /eqnqtdec
            /nat_rec /nat_rect  /list_rect /eq_rect_r /eq_rect /eq_sym /f_equal
            /eq_ind_r /eq_ind /eq_nat /eq_sym /ts in h3;
  let np := type of h3 in
  let nnp := orename st np in
  try (change nnp in h3);
 (*    rewrite ?/ts /coerce /wsort /trl3 /tr3 /f3 /o3_norm /cT /cB in h3;
   rewrite /convert /trs ?eqnqtdec_refl /eq_rect_r /eq_rect /Logic.eq_sym in h3;
   rewrite /appist /trs /eqnqtdec /eq_rect_r /eq_rect /nat_rec /nat_rect /protect_term  /eq_ind_r /eq_ind /eq_sym /f_equal /wsort /sl in h3; *)
  clear ts;
  simplify_hyp h3;
try discriminate.



Ltac rew_dnd_hyp fl  h1 h2 h3 hp1 hp2 hp2' t i :=
  let ht1 := type of h1 in
  let ht2 := type of h2 in
  let ts1 := mkSign hp1 ht1 in
  let ts := mkSignR ts1 hp2  (fun XX : (forall TT:Type, TT) => ht2) in
      rew_dnd_hyp_o ts fl  h1 h2 h3 hp1 hp2 hp2' t i.
(*
  let th1 := type of h1 in
  let th2 := type of h2 in 
  let ts2 := mkSign ts'' hp1 th1 in 
  let ts := mkSign ts2 hp2 th2 in
  let diff := find_comp ts'' ts in 
  let e := constr:(refl_equal ts) in
  let i' := constr:(magic_l ts ts'' diff e i) in
  let i'' := eval hnf in i' in       
  rew_dnd_hyp_o ts fl  h1 h2 h3 hp1 hp2 hp2' t i''.
*)

  
(*
Parameter P : nat -> Prop.
Parameter B C : Prop.

Goal (B -> 3=4) -> P 3 -> C.
intros h p.      

rew_dnd_hyp
  test
  true
  h
  p
  p'
  (cons true nil)
  (@nil bool)
  (cons 0 nil)
  (cons true ( (cons false nil)))
  (@nil (option (inst2 test))).
 *)

Ltac forward_o ts' h1' h2' h3 hp1 hp2 t i :=
  let ts1 := eval compute in ts' in
  let ts := fresh "ts" in
  pose ts := ts1;
  let h1 := fresh "_fh1" in
  let h2 := fresh "_fh2" in
  move: (h1') => h1;
  move: (h2') => h2;
  reify_hyp ts hp1 h1;
  reify_hyp ts hp2 h2;
  let o1 := type of h1 in
  let o2 := type of h2 in 
  match o1 with
  | coerce _ (@nil nat) ?hc1 _ => 
    match o2 with
    | coerce _ (@nil nat) ?hc2 _  => 
        let i' := dress ts i in
            move:
           (f3_corr ts true  t false i' (@nil nat) hc1 tt
                    (@nil nat) hc2 tt h1 h2) => h3
        end
  end;
  apply trex_norm_fapply in h3;
  rewrite /coerce  /= in h1;
  rewrite /coerce /= in h2;
  [ | simpl; try done; auto];
  try clear h1; try clear h2;
  let st := match type of h3 with
            | trl3 _ ?oh => oh
            end in
  rewrite  /f3 /o3_norm /trl3  /coerce /xor /tr3  /check_curry
           /check_list
           /eq_list /list_rec /eq_rect_r /eq_rec_r /eq_rect /eq_sym
           /seq.cat
           /check_nat
           /eq_nat /eqnqtdec  /app_curry /nat_rec /nat_rect
           /eq_rect_r /eq_rect /eq_rec_r
           /eq_ind_r /eq_ind  /eq_sym /list_rect
           /eq_rect_r /eq_rect /eq_sym /ppconcat
           /ts  /wsort /sl
     /eq_rec_r /eq_sym /eq_rec /eq_rect in h3;
    let np := type of h3 in
    let nnp := orename st np in
    try change nnp in h3;
    simplify_hyp h3;
  try clear ts;
    try discriminate.

Ltac forward  h1' h2' h3 hp1 hp2 t i :=
  let t1 := type of h1' in
  let t2 := type of h2' in
  let ts1 := mkSign hp1 t1 in
  let ts := mkSignR ts1  hp2  (fun XX : (forall TT:Type, TT) => t2) in
      forward_o ts h1' h2' h3 hp1 hp2 t i.

      (* /trl3 /f3 /o3_norm  /trad /trad1 /appist /trl3 /tr3 /convert /cT /cB /trad /trad1 /seq.nth /nthc /list_rect  /wsort
   rewrite /trs /sl /ts  /trs /sl  /eqnqtdec /protect_term /nat_rec /nat_rect /seq.nth /nthc /list_rect /eq_sym
                  ?eqnqtdec_refl /eq_rect_r
                  /eq_rect /eq_ind_r /eq_ind /Logic.eq_sym /eq_sym /trad1 /coerce
                  ?eqnqtdec_refl /eq_rect_r /eq_rect /Logic.eq_sym /trad1 /trs /eq_rect_r in h3; *)

(*
Goal 2=3 -> 3=4.
  intro h.
  Check b3_corr.
  Check andr.

  Check
    ltac:(let r :=
            reify_eq_rec test
                         (@nil bool)(@nil nat)(@nil DYN)(3=4)
                         in exact r).
 

rew_dnd test  h (@nil bool)(cons 1 nil)(@nil bool)(cons true nil)(@nil (option (inst2 test))).
Abort.


Definition iin  : nat -> list (option (inst2 test)).
  intro n.
apply cons; last apply nil.
apply Some; exists 0.
move => *; exact n.
Defined.


Definition idd : list (option (inst2 test)).
apply cons; try apply nil.
apply Some.
exists 0.
intros e1 e2.
apply e2.
exact 0.
Defined.
           

(*
Goal (forall x, x+0 = x) -> forall y, 0+y = y+0.
  move => h.
rew_dnd test h (cons false nil)
        (cons 2 nil)
        (cons false nil)
        (cons true (cons false (cons false nil)))
        idd.
Abort.


(* false -> *)

Goal (forall x:nat, x = 4) -> (nat -> 1+2 = 4) -> False.
  move => h1 h2.

  
  
  rew_dnd_hyp test h1 h2 h3
            (cons false nil)
            (cons false nil)
            (cons 2 nil)
            (cons true (cons false (cons false nil))) (cons None (iin (1+2))).
Abort.

Parameter P Q : nat -> Prop.

Goal (forall x, P x -> Q x) -> forall y, Q y.
intro h.


back test  h (cons false (cons true nil))(cons false nil)
     (cons true (cons false (cons false nil)))
     idd.
Abort.


Definition ip0 : option (inst2 test).
apply Some.
exists 2.
intros; exact (P 0).
Defined.

Goal (forall X:Prop, X) -> P 0.
intro h.
back test h (cons false nil)(@nil bool)(cons false nil)(cons ip0 nil).
Abort.





Definition empty : inst' test.
apply nil.
Defined.

Parameter A B C D : Prop.

Goal (A -> B) ->(B/\A) ->  B /\ A.
  intros b c.


  forward test  c b d   (cons true nil) (cons false nil) (cons true (cons false nil)) empty.
Abort.

Goal ~A -> A -> B.
  move => na a.
  
forward test  na a ff
        (cons false nil)
        (@nil bool)
        (cons false nil)
        empty.
Abort.

Definition ii : inst' test.
apply cons.
2 : apply nil.
apply Some.
unfold inst2.
exists 1.
unfold env.
intros e1 e2.
apply e1.
apply 0.
Defined.


Goal (forall z:bool, true=z) -> forall x:bool,forall y,(true=x \/ y=2).
  intros h.


  
  back test  h (cons false nil) (cons false (cons false (cons false nil))) (cons true (cons true (cons false (cons true nil)))) ii.
Abort.





Goal (2=2 /\ 3=3) ->  (2=2 /\ 3=3).
  intro xx.
  
back test xx  ((cons false (@nil bool)))
     ((cons false (@nil bool)))
     (cons true (cons false nil)) empty.

back test  xx  ( (cons false (@nil bool)))  ( ( (@nil bool))) (cons false ( nil)) empty.
Abort.

(* for testing and playing : some inst *)
Definition ex_ex : inst' test.
apply cons; last apply nil.
apply None.
Defined.
Definition ex_ex' : inst' test.
apply cons; last apply nil.
apply Some.
exists 0.
intros e1 e2; apply e1.
exact 0.
Defined.

Definition ex_ex2 : inst test.
unfold inst.
apply (cons None).
apply (cons None).
apply nil.
Defined.


Goal (exists x, x=2 /\ 3=3) -> exists y, y=2 /\ 3=3.
  move => xx.

  

  back test xx  [::false; true]  [::false; true]
       [::true; false; false ; true] ex_ex.


  back test xx  [::false; false]  [::false]
      [::false; true; false] ex_ex'.
Abort.
*)
  
(*
(* I leave this here for now but probably not useful *)  
Definition sb3 l li nh h ih ng g ig :=
  simpl3 (b3 l li nh h ih ng g ig).

Definition sf3 l li nh h ih ng g ig :=
  simpl3 (f3 l li nh h ih ng g ig).

Lemma sb3_corr_l :
 forall l ist nh hyp hi ng goal gi,
         (tr3 (sb3 l ist nh hyp hi ng goal gi))
            -> (coerce _ hyp hi) -> (coerce _ goal gi).
  move => l ist nh hyp hi ng goal gi c1 c2.
  case: (b3_corr l)=> [hc _].
apply (hc ist nh hyp hi); last done.
by apply simpl3_do2.
Qed.

Lemma sb3_corr :
 forall l ist hyp goal,
         (tr3 (sb3 l ist 0 hyp I 0 goal I))
            -> (coerce _ hyp I) -> (coerce _ goal I).
by intros l ist hyp goal *; apply (sb3_corr_l l ist 0 hyp I).
Qed.

  Check b3_corr.

Lemma sf3_corr_l :
   forall l (ist : inst) (n1 : nat) (h1 : cx n1) (i1 : pp n1) 
          (n2 : nat) (h2 : cx n2) (i2 : pp n2),
        coerce n1 h1 i1 -> coerce n2 h2 i2 -> tr3 (sf3 l ist n1 h1 i1 n2 h2 i2).
  move => l ist nh hyp hi ng goal gi c1 c2.
  case: (b3_corr l)=> [_ hc].
 apply simpl3_do1.
by apply (hc ist nh hyp hi).
Qed.

Lemma sf3_corr :
  forall l inst h1 h2,
    coerce 0 h1 I -> coerce 0 h2 I -> tr3 (sf3 l inst 0 h1 I 0 h2 I).
 by intros l ist h1 h2 *; apply (sf3_corr_l l ist 0 h1 I).
Qed.
 *)
 *)
  
Ltac myinduction_r  p t :=
  match p with
  | nil =>   t
  | cons ?n ?p' =>
      match t with
      | ?a -> ?b =>
          let c := constr:(imp_fun a b) in
          let c' := myinduction_r p c in
          c'
      |  forall x: ?T, @?body' x => 
             let y := fresh "y" in
             lazymatch
               constr:(fun y : T =>
                      ltac:(
                              let body := beta1 body' y in
                              let r := myinduction_r p' body in exact r))
        with                    
        | (fun _ : _ => ?r2) => r2
             end
      |  exists x: ?T, @?body' x => 
             let y := fresh "y" in
             lazymatch
               constr:(fun y : T =>
                      ltac:(
                              let body := beta1 body' y in
                              let r := myinduction_r p' body in exact r))
        with                    
        | (fun _ : _ => ?r2) => r2
             end
      | fun x : ?T => @?body' x => 
             let y := fresh "y" in
             lazymatch
               constr:(fun y : T =>
                      ltac:(
                              let body := beta1 body' y in
                              let r := myinduction_r p' body in exact r))
        with                    
        | (fun _ : _ => ?r2) => r2
             end
      | (?f0 _) =>
          let l := list_args t in
          let u := myinduction_r p' ltac:(extract ltac:(tnth l (S n))) in
          u
      end
  end.


Ltac definduction :=
   match goal with
   | |- forall x : _, _ =>
       let nx := fresh x in
       intro nx; induction nx
   | _ => 
       let arg := fresh "arg" in
       intro arg; induction arg
   end.


Ltac ninduction n :=
  match constr:(n) with
  | 0 => definduction
  | S ?m => intro; ninduction m
  end.

Ltac pinduction p :=
  match p with
  | nil => definduction
  | cons _ ?p' => intro; pinduction p'
  end.

Ltac cdr l :=
  match l with
  | cons 0 ?l' => l'
  end.

Ltac myinduction p :=
  match goal with
  | |- ?g =>
      let g' := myinduction_r p g in
      induction g'
  | _ => pinduction p
  | _ => pinduction ltac:(cdr p)
  end;
  simplify_goal;
try discriminate.

Ltac myinduction_hyp h p :=
  let g := type of h in
  let g' := myinduction_r p g in
  induction g';
  simplify_goal;
  try discriminate.

Ltac defcase :=
   match goal with
   | |- forall x : _, _ =>
       let nx := fresh x in
       intro nx; destruct nx
   | _ => 
       let arg := fresh "arg" in
       intro arg; destruct arg
   end.

Ltac pcase p :=
  match p with
  | nil => defcase
  | cons _ ?p' => intro; pcase p'
  end.


Ltac mydestruct e t:=
  generalize (refl_equal t);
  destruct t at -1;
  intro e.

Ltac mycase p :=
  match goal with
  | |- ?g =>
      let g' := myinduction_r p g in
      let e := fresh "e" in
      mydestruct e g'
  | _ => pcase p
  | _ => pcase ltac:(cdr p)
  end;
  simplify_goal;
try discriminate.


Ltac mycase_hyp h p :=
  let e := fresh "e" in
  let g := type of h in
  let g' := myinduction_r p g in
  mydestruct e g';
  simplify_goal;
  try discriminate.


Ltac myinduction_nosimpl p :=
  match goal with
  | |- ?g =>
      let g' := myinduction_r p g in
      induction g'
  | _ => pinduction p
  | _ => pinduction ltac:(cdr p)
  end.

Ltac myinduction_hyp_nosimpl h p :=
  let g := type of h in
  let g' := myinduction_r p g in
  induction g'.


(*
      let g' := myinduction_r p g in
      match g' with
      | forall n : _, _ => pinduction p
      | _ -> _ => pinduction p
      | _ => induction g'
      end
  end.
 *)
Ltac ttest t :=
  match t with
  | forall z : ?A, ?t' =>
      let t'' := constr:(subst! true for z in t') in
                          let r := (ttest t'') in
                          constr:(S r)
  | _ => constr:(0)
  end.

Check ltac:(let r := ttest    (forall x : nat, forall y, x = y)
in exact r).

              
Ltac build_context_r t p l :=
  match p with
  | nil => constr:(l)
  | cons ?n ?p' =>
      match t with
      | forall x : ?A, ?t' =>
          let l' := aDYN A l in
          build_context_r (subst! true for x in t') p' l'
      | exists x : ?A , ?t' =>
          let l' := aDYN A l in
          build_context_r  (subst! true for x in t') p' l'
      | ?A /\ ?B =>
          match n with
          | 0 =>  build_context_r A p' l
          | _ => build_context_r B p' l
          end
      | ?A \/ ?B  =>
          match n with
          | 0 =>  build_context_r A p' l
          | _ => build_context_r B p' l
          end
      | ?A -> ?B  =>
          match n with
          | 0 =>  build_context_r A p' l
          | _ => build_context_r B p' l
          end
      | ~ ?A  => build_context_r A p' l

      | _ => l
      end
  end.

Ltac build_context t p :=
build_context_r t p (@nil TDYN).

            
Ltac point_goal t p :=
  match p with
  | nil => ltac:(t)
  | cons 0 ?p' =>
      match goal with
      | |- (_ /\ _) => split; [ point_goal t p' | t]
      | |- (_\/_) => left; point_goal t p'
      | |- (_ -> _) =>
          let h := fresh "h" in
          intro h; point_hyp h t p'
      | |- forall x : _, _ =>
          intro x; point_goal t p'
      | |- ~ _ =>
          let h := fresh "h" in
          intro h; point_hyp h t p'
      |  _ => idtac
      end
  | cons _ ?p' =>
      match goal with
      | |- (_ /\ _) => split; [t | point_goal t p']
      | |- (_\/_) => right; point_goal t p'
      | |- (_ -> _) => intro;  point_goal t p'
      | _ => idtac
      end
  end
with point_hyp h t p :=
    match p with
    | nil => ltac:(t)
    | cons 0 ?p' =>
        match type of h with
        | (_ /\ _) =>
            let h' := fresh "h" in
            move: (h) => [h' _];                         
             point_hyp h' t p';
             match p' with
             | nil => idtac
             | _ => clear h'
             end
        | (?A -> _) =>
            let a := fresh "a" in
            cut A; [move => a; move/(_ a): h => h|
                     point_goal t p']
        | exists x : _, _ =>
            let h' := fresh "h" in
            move: (h) => [x h'];
            point_hyp h' t p'
        | ~ _ =>
          case h; point_goal t p'
      |  _ => idtac
        end
    | cons _ ?p' =>
        match type of h with
        | (_ /\ _) =>
            let h' := fresh "h" in
            move: (h) => [_ h'];
             point_hyp h' t p';
             match p' with
             | nil => idtac
             | _ => clear h'
             end
       | (?A -> ?B) =>
            let a := fresh "a" in
            cut A;
            [move => a; move/(_ a): h => h;
             point_hyp h t p' | t]
        | _ => idtac    
        end
    end.

Ltac shoot := trivial.

Ltac pbp p := point_goal shoot p.

Ltac pbp_hyp h p := point_hyp h shoot p.

Ltac rew_all_left h :=
  match type of h with
  | ?a = ?b =>
      is_var a;
      rewrite -> h in *; clear h
  | ?a = ?b => rewrite -> h in *
  | _ => idtac
  end.

Ltac rew_all_right h :=
    match type of h with
  | ?a = ?b =>
      is_var a;
      rewrite -> h in *; clear h
  | ?a = ?b => rewrite <- h in *
  | _ => idtac
  end.
