(****************************)
(*                          *)
(*  Benjamin Werner         *)
(*                          *)
(****************************)



Require Import ssreflect.


(* tuples of objects (for now we are mono-sorted with objects in nat *)

Fixpoint pp (n : nat) : Type :=
  match n with
  | 0 => True
  | S n => nat * (pp n)
end.


(* focused propositions with n free variables *)

Inductive cx : nat -> Type :=
| cTop : forall n,  cx n
| cBot : forall n,  cx n
| Hole : forall n,  ((pp n) -> Prop) -> (cx n)
| impr : forall n, ((pp n) -> Prop) -> (cx n) -> (cx n)
| impl : forall n, (cx n) -> ((pp n) -> Prop) -> (cx n)
| orr : forall n, ((pp n) -> Prop) -> (cx n) -> (cx n)
| orl : forall n, (cx n) -> ((pp n) -> Prop) -> (cx n)
| andr : forall n, ((pp n) -> Prop) -> (cx n) -> (cx n)
| andl : forall n, (cx n) -> ((pp n) -> Prop) -> (cx n)
| fa : forall n, cx (S n) -> cx n
| ex : forall n, cx (S n) -> cx n
| equality : forall n,
    ((pp n) -> nat) ->((pp n) -> nat) -> cx n
| property  : forall n,
    ((pp (S n)) -> Prop) ->
    ((pp n) -> nat)  -> cx n.


(* constant cx's *)
Fixpoint ppc (P:Prop)(n : nat): (pp n) -> Prop :=
  match n with
  | 0 => fun _ =>  P
  | S m => fun (c:(pp(S m))) =>
             match c with
               pair _ d  =>  (ppc P m d)
             end
  end.

Lemma ppce : forall P n c,  ppc P n c = P.
  move=> P; elim => [//=|n hn][c1 c2]/=.
  by rewrite hn.
Qed.


(* translating back into Prop *)

Fixpoint coerce  (n:nat) (c:cx n) : (pp n) -> Prop :=
  match c with
| cTop _ => ppc True _
| cBot _ => ppc False _
| Hole _ P => P
| impl _ c P => fun x => ((coerce _ c x)  -> (P x))
| impr _ P c => fun x =>  (P x) -> (coerce _ c x)
| orl _ c P => fun x => (coerce _ c x)\/(P x)
| orr _ P c => fun x =>  (P x) \/ (coerce _ c x)
| andl _ c P => fun x => (coerce _ c x) /\ (P x)
| andr _ P c => fun x =>  (P x) /\ (coerce _ c x)
| fa _ c => fun x =>  forall p:nat, (coerce _ c (p, x))
| ex _ c => fun x =>  exists p:nat,  (coerce _ c (p, x))
| equality _ t u =>fun x =>
                       (t x) = (u x)
| property _ P t => fun x =>
                        ( P ((t x),x))
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

Fixpoint simpl n (c : cx n) : cx n :=
  match n, c with
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
  | n, fa _ A =>
      match (cT _ (simpl _ A)) with
      | true => cTop _
      | _ => fa _ (simpl _ A)
      end 
  | n, ex _ A =>
      match (cB _ (simpl _ A)) with
      | true => cBot _
      | _ => ex _ (simpl _ A)
       end 
  | n, cBot _ => cBot _
  | n, cTop _ => cTop _
  | n, h => h
  end.

(* We need to show equivalence first *)

Lemma simpl_corr : forall n c i, coerce n c i <-> coerce n (simpl n c) i.
  move=> m c.

  elim: {m} c  =>
        [n|n|n P|n A B hB|n A hA B|n A  B hB|n A hA  B
        |n A B hB|n A hA B|n A hA |n A hA|n t u|n P t] i //=;
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


Lemma simpl_step :  forall n c i, coerce n (simpl n c) i -> coerce n c i.
by move => n c i; case (simpl_corr n c i).
Qed.

(* will indicate which deep operations to perform *)
Definition trace := (list bool).

Fixpoint def n : pp n :=
  match n with
  | 0 => I
  | S n => (0, (def n))
  end.

(* to avoid problems with type dependency *)

Fixpoint convert n m (i: pp n) : pp m :=
  match n, i, m with
  | 0, I, m => (def m)
  | S n, i, 0 => (def 0)
  | S n, (x,i), S m => (x, (convert n m i))
  end.


Lemma convert_corr : forall n i,  convert n n i = i.
elim => [//=|n hn] []//= a b.
by rewrite hn.
Qed.

(* The result type of interactions (deep inference) *)

Inductive o3 : Type :=
  Hol3 : Prop -> o3
| top3
| bot3
| impl3 : o3 -> Prop -> o3
| impr3 : Prop -> o3 -> o3
| orl3 : o3 -> Prop -> o3
| orr3 : Prop -> o3 -> o3
| andr3 : Prop -> o3 -> o3
| andl3 : o3 -> Prop -> o3
| fa3 : (nat -> o3) -> o3
| ex3 : (nat -> o3) -> o3.

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
  | fa3 p =>  forall n,   (tr3 (p n))
  | ex3 p => exists n, (tr3 (p n))
  | top3 => True
  | bot3 => False
  end.

Lemma tH : forall P,  tr3 (Hol3 P) = P.
done.
Qed.

Lemma til : forall o P,  tr3 (impl3 o P) = ((tr3 o) -> P).
  done. Qed.



(* the datatype which will indicate whether encoutered quantified
   variables are instantiated and by what *)

Definition inst :=
  list (option ({n1 : nat & {n2 : nat & (pp n1)->(pp n2) -> nat}})).

(* using an inst *)
Definition appist
           (f:{n1 : nat & {n2 : nat & (pp n1)->(pp n2) -> nat}})
           n1 (i1 : pp n1) n2 (i2 : pp n2) :=
  match f with
    existT _ m1 (existT _ m2 f) =>
      f (convert n1 m1 i1)(convert n2 m2 i2)
                       end.

(*
Parameter f :(pp 4)->(pp 3) -> nat.
Eval compute in (pp 4).
Eval compute in
  (appist (existT
             (fun x => {n2 : nat & (pp x)->(pp n2) -> nat})
             4 (existT (fun x =>(pp 4)->(pp x)-> nat)  3 f)) 4 (1,(2,(3,(4,I))))) 4 (5,(6,(7,(8,I)))).
*)



(* the main functions as described in our CPP 2022 article *)

Fixpoint b3 (l:trace)(ist:inst)(nh:nat)(hyp : cx nh)(hi : pp nh)
         (ng : nat)(goal : cx ng)(gi : pp ng) : o3 :=
  match l  with
  | nil =>
      match hyp, goal with
      | (Hole nh' h), (Hole ng' g) =>
          (Hol3  ((h (convert nh nh' hi))->
                  (g (convert ng ng' gi))))
      | _,_ => bot3
      end
  | (cons true l) =>
      match goal return o3 with
      | (property ng' P v) =>
          match hyp with
          | (equality nh' t u) =>
              andl3  
                (Hol3 ((u (convert nh nh' hi))
                 =(v (convert ng ng' gi))))
                 (P ((t (convert nh nh' hi)),(convert ng ng' gi)))
          | _ => bot3
          end

      | (impl ng' h B) =>
          (impl3 (f3 l ist nh hyp hi ng' h (convert ng ng' gi))
                 (B (convert ng ng' gi)))

      | (impr ng'  B g) =>
          (impr3 (B (convert ng ng' gi))
                 (b3 l ist nh hyp hi _ g (convert ng ng' gi)))

      |  (fa ng' g) =>
               fa3 (fun n=>
                  (b3 l ist nh hyp hi (S ng') g
                               (convert (S ng) (S ng') (n, gi))))
    | orl ng' g B =>
          orl3 (b3 l ist nh hyp hi _ g (convert ng ng' gi))
               (B (convert ng ng' gi))
      | orr ng' B g =>
          orr3  (B (convert ng ng' gi))
                (b3 l ist nh hyp hi _ g (convert ng ng' gi))
      | andl ng' g B =>
          andl3 (b3 l ist nh hyp hi _ g (convert ng ng' gi))
               (B (convert ng ng' gi))
      | andr ng' B g =>
          andr3  (B (convert ng ng' gi))
                 (b3 l ist nh hyp hi _ g (convert ng ng' gi)) 
      | ex ng' g =>
          match ist with
          | cons (Some f) ist =>
              b3 l ist
                 nh hyp hi
                 (S ng') g
                 (convert (S ng)(S ng')
                          ((appist f nh hi ng gi),gi))
          |  cons None ist =>
               ex3
                 (fun p =>
                    b3 l ist nh hyp hi
                       (S ng') g
                       (convert (S ng)(S ng')
                                (p,gi)))
          | nil => bot3
          end
                
      | cTop _ => top3
                     
      | cBot _ => bot3
      | Hole _ _ => bot3
      | _ => bot3
      end
  | (cons false l) =>
      match hyp with
          | (equality nh' t u) =>
              match goal with
              | (property ng' P v) =>
                 andl3 (Hol3
                    ((t (convert nh nh' hi))
                     =(v (convert ng ng' gi))))
                       (P ((u (convert nh nh' hi)),(convert ng ng' gi)))
          | _ => bot3
              end

        
      | andl nh' h B =>
           (b3 l ist nh' h (convert nh nh' hi)
                    ng goal gi)
      | andr nh' B h =>
                 (b3 l ist nh' h (convert nh nh' hi)
                     ng goal gi)
      | orl nh' h B =>
          andl3 (b3 l ist nh' h (convert nh nh' hi)
                   ng goal gi)
               ((B (convert nh nh' hi))->
                (coerce _ goal gi))
      | orr nh' B h =>
          andr3 ((B (convert nh nh' hi))->
                (coerce _ goal gi))
               (b3 l ist nh' h (convert nh nh' hi)
                   ng goal gi) 
      | impr nh' B h =>
          andr3 (B (convert nh nh' hi))
                (b3 l ist nh' h (convert nh nh' hi)
                   ng goal gi)
      | fa n h =>
          match ist with
          | cons (Some f) ist =>
              (b3 l ist
                  (S n) h (convert
                         (S nh) (S n)
                         ((appist f nh hi ng gi),hi))
                  ng goal gi)
          | _ => bot3
          end
      | ex n h =>
          fa3
            (fun p =>
               (b3 l ist
                   (S n) h
                   (convert (S nh)(S n)
                            (p, hi))
                   ng goal gi))
      | impl  _ _ _  => bot3
      | cTop _ => bot3
      | cBot _ => top3
      | Hole _ _ => bot3
      | _ => bot3
      end
  end
with f3 (l:trace)(ist: inst)(n1:nat)(h1 : cx n1)(i1 : pp n1)
        (n2 : nat)(h2 : cx n2)(i2 : pp n2) :
      o3 :=
  match l with
  | nil => top3
  | cons false l =>
      match h1 with
      | equality n1' t u =>
          match h2 with
          | property n2' P v =>
              Hol3
                ((v (convert n2 n2' i2)  = u (convert n1 n1' i1))
                ->
              P (convert (S n2)(S n2')(t (convert n1 n1' i1), i2)))
          | _ => top3
          end
      | andl n1' h1' B =>
          f3 l ist n1' h1' (convert n1 n1' i1) n2 h2 i2
      | andr n1' B h1' =>
          f3 l ist n1' h1' (convert n1 n1' i1) n2 h2 i2
     | orl  n1' h1' B =>
          orl3  (f3 l ist n1' h1' (convert n1 n1' i1) n2 h2 i2)
                (B (convert n1 n1' i1))
      | orr n1' B h1' =>
          orr3 (B (convert n1 n1' i1))
               (f3 l ist n1' h1' (convert n1 n1' i1) n2 h2 i2) 
      | impl n1' h1' B =>
          impl3 (b3 l ist n2 h2 i2 n1' h1' (convert n1 n1' i1)) (B (convert n1 n1' i1))
      | impr n1' B h1' =>
          impr3  (B (convert n1 n1' i1))
                 (f3 l ist n1' h1' (convert n1 n1' i1) n2 h2 i2)
      | fa n1' h1' =>
          fa3 (fun n =>
                 (f3 l ist (S n1') h1' (convert (S n1)(S n1') (n, i1))
                          n2 h2 i2)) 
          
      | _ => top3
      end
   | cons true l =>
       match h2 with
                     
       | property n2' P v =>
           match h1 with
          | equality n1' t u =>
              Hol3
                ((v (convert n2 n2' i2)=t (convert n1 n1' i1))->
              P (convert (S n2)(S n2')(u (convert n1 n1' i1), i2)))
          | _ => top3
          end
    

      | andl n2' h2' B =>
          f3 l ist n1 h1 i1  n2' h2' (convert n2 n2' i2)
      | andr n2' B h2' =>
          f3 l ist n1 h1 i1 n2' h2' (convert n2 n2' i2)
     | orl  n2' h2' B =>
          orl3 
               (f3 l ist n2' h2' (convert n2 n2' i2)
                n1 h1 i1) (B (convert n2 n2' i2)) 
      | orr n2' B h2' =>
          orr3 (B (convert n2 n2' i2))
               (f3 l ist n1 h1 i1 n2' h2' (convert n2 n2' i2)) 
      | impl n2' h2' B =>
          impl3 (b3 l ist n1 h1 i1 n2' h2' (convert n2 n2' i2)) (B (convert n2 n2' i2))
      | impr n2' B h2' =>
          impr3  (B (convert n2 n2' i2))
                 (f3 l ist n1 h1 i1 n2' h2' (convert n2 n2' i2) )
      | fa n2' h2' =>
          fa3 (fun n =>
                 (f3 l ist n2 h2 i2
                          (S n2') h2' (convert (S n2)(S n2') (n, i2))
                         )) 
          
      | _ => top3
      end
  end   .

(*
Parameter A B : Prop.

Definition h := (Hole 0 (fun _ => A)).

Definition g1  := (impr _ (fun _ => B) h).
Definition h1 := impl _ h (fun _ => B).
Check g1.


Eval compute in (tr3 (b3 (cons true nil) nil 0 h I 0 g1 I)). 
Eval compute in (tr3 (f3 (cons false nil) nil 0 h1 I 0 h I)). 

Definition g2  := fa 0  (Hole 1 (fun _ =>  A)).





Eval compute in (b3 (cons true nil) nil 0 h I 0 g2 I). 

Eval compute in (tr3 (b3 (cons true nil) nil 0 h I 0 g2 I)). 
Eval compute in (tr3 (b3 (cons true nil) nil 0 h I 0 g1 I)). 
*)


Lemma bf3_corr :
  forall l,
    (forall ist nh hyp hi ng goal gi,
         (tr3 (b3 l ist nh hyp hi ng goal gi))
            -> (coerce _ hyp hi) -> (coerce _ goal gi))
    /\
      (forall ist n1 h1 i1 n2 h2 i2,
          (coerce _ h1 i1) -> (coerce _ h2 i2) ->
          (tr3 (f3 l ist n1 h1 i1 n2 h2 i2))).


elim => [//=|[|] l hl]/=; split; try done;
   try move: hl => [hl1 hl2].

move => _ 
[|n2]
        [nh'|nh'|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
        |nh' P h|nh' h P|nh' h|nh' h|nh' t u|nh P v]//= hi
 [|ng]
          [ng'|ng'|ng' Q|ng' Q g|ng' g Q|ng' Q g|ng' g Q
          |ng' Q g|ng' g Q|ng' g|ng' g|ng' t' u'|ng' P' v'] gi //=;
rewrite  /= ?convert_corr ?ppce//=; move => [-> h2] e//=.


move => ist nh hyp hi
          [|ng]
          [ng'|ng'|ng' Q|ng' Q g|ng' g Q|ng' Q g|ng' g Q
          |ng' Q g|ng' g Q|ng' g|ng' g|ng' t u|ng' P v] gi //=;
  rewrite /= ?convert_corr ?ppce//=; eauto;
        case: ist => [|[a|] ist]//=; eauto;
    intros h1 h2; eauto;
 try (by move: h1 => [p hp]; exists p; eauto);
 try (by move: h1 => [h1|h1];  eauto);
 try (by move: h1 => [h11 h12];  eauto);

move: nh hyp hi h1 h2;
move => [|n2]
        [nh'|nh'|nh' Q|nh' Q h|nh' h Q|nh' Q h|nh' h Q
        |nh' Q h|nh' h Q|nh' h|nh' h|nh' t u|nh Q v']//= hi';
        rewrite ?convert_corr;
      try (by move => [<- h] <-).


move => ist n1 h1 i1 n2 h2 i2 hr1 hr2.
move: n2 h2 i2 hr2.
move=>[|n2]
        [nh'|nh'|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
        |nh' P h|nh' h P|nh' h|nh' h|nh' t u|nh' P v]//= P2 i2;
      rewrite convert_corr; eauto;
try (by case: i2; eauto); 
move: n1 h1 i1 hr1 => [|n1][n1'|n1'|n1' Q|n1' Q h|n1' h Q|n1' Q h
           |n1' h Q|n1' Q h|n1' h Q|n1' h|n1' h|n1' t u|n1' Q w] i1 //=;
 by rewrite convert_corr => <- <-. 

move => ist [|nh][nh'|nh'|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
                 |nh' P h|nh' h P|nh' h|nh' h|nh' t u|nh' P v]//= hi ng goal gi;
        try rewrite  convert_corr; eauto;
        try (by case;eauto);
        try (by move => [h1 h2][h3 h4]; eauto);
   try (by move: ist => [|[f|] ist]//= h1 hp; eauto);
   try (by move=> hn [p hp]; eauto);
   try (by move=> [h1 h2][h3|h3]; eauto);
   try (by rewrite ppce);
move: ng goal gi =>
  [|ng] [ng'|ng'|ng' Q|ng' Q g|ng' g Q|ng' Q g|ng' g Q
        |ng' Q g|ng' g Q|ng' g|ng' g|ng' t' u'|ng' P v'] gi //=;
        
rewrite ?convert_corr;
move => [<- p] ->; done.


move => ist n1 h1 i1 n2 h2 i2 p1 p2.
move: n1 h1 i1 p1 =>
      [|nh][nh'|nh'|nh' P|nh' P h|nh' h P|nh' P h
           |nh' h P|nh' P h|nh' h P|nh' h|nh' h|nh' t u|nh' P v] i1 //=;
 rewrite convert_corr; eauto;
  try (by case;eauto);

 move => <-;
move: n2 h2 i2 p2;
move=>[|n2]
        [n2'|n2'|n2' P|n2' P h|n2' h P|n2' P h|n2' h P
        |n2' P h|n2' h P|n2' h|n2' h|n2' t' u'|n2' P v']//= P2 i2;
      rewrite convert_corr; eauto;
      try (by case: i2; eauto);
      move => <- //=.

Qed.



Definition trl3 := nosimpl tr3.

Lemma b3_corr :  forall l : trace,
       (forall (ist : inst) (nh : nat)  (hi : pp nh) (ng : nat) (gi : pp ng)
          (hyp : cx nh)
            (goal : cx ng), trl3 (b3 l ist nh hyp hi ng goal gi) -> coerce nh hyp hi -> coerce ng goal gi).
move => l ist nh hi ng gi hyp goal.  
case: (bf3_corr l) => [h _]; apply h.
Qed.

Lemma s3_corr : forall l (ist : inst) (n1 : nat) (h1 : cx n1) (i1 : pp n1) 
          (n2 : nat) (h2 : cx n2) (i2 : pp n2),
        coerce n1 h1 i1 -> coerce n2 h2 i2 -> trl3 (f3 l ist n1 h1 i1 n2 h2 i2).
move => l ist n1 h1 i1 n2 h2 i2.
case: (bf3_corr l) => [_ h]; apply h.
Qed.
  

(* Socrates example *)
Parameter H M : nat -> Prop.

Definition hm := forall x,  H x -> M x.
Definition hs := H 0.

Definition gs := M 0.

Definition fhs := Hole 0 (fun _ => gs).

Definition fgs := fa 0 (impr 1
                             (fun x => let (n,_):=x in (H n))
                             (Hole 1 (fun x => let (n,_):=x in (M n)))).


Definition iS : inst.
  apply cons; try apply nil.
  apply Some.
  exists 0; exists 0 => _ _; exact 0.
Defined.  

Eval compute in
  (trl3 (b3 (cons false (cons false nil)) iS 0 fgs I 0 fhs I)).


(* not sur this will be useful *)

(*
Fixpoint trans (n:nat)(c : cx n)(gi : pp n) : o3 :=
  match n, c, gi with
  | n, Hole _ P, gi => Hol3(P gi)
  | n, impr _ P c, gi => impr3 (P gi)(trans _ c gi)
  | n, impl _ c P, gi => impl3 (trans _ c gi)(P gi)
  | n, orr _ P c, gi => orr3 (P gi)(trans _ c gi)
  | n, orl _ c P, gi => orl3 (trans _ c gi)(P gi)
  | n, andr _ P c, gi => andr3 (P gi)(trans _ c gi)
  | n, andl _ c P, gi => andl3 (trans _ c gi)(P gi)
  | n, fa _ c, gi => fa3 (fun p =>  (trans (S _) c (p,gi)))
  | n, ex _ c, gi => ex3 (fun p =>  (trans (S _) c (p,gi)))
  | n, cTop _, _ => top3
  | n, cBot _, _ => bot3
  end.


Lemma cx_o3 : forall n c gi, (coerce n c gi)<->(tr3 (trans n c gi)).
  induction c; simpl => gi; rewrite ?ppce;
                        split; auto;
                        try (by intuition);
                        try (case: (IHc gi) => [h1 h2]);
                        try split; auto;
                        auto;
                        try by intuition.
  move=> hn p;case: (IHc (p,gi)) => [h1 h2];  intuition.
  move=> hn p;case: (IHc (p,gi)) => [h1 h2];  intuition.
move => [p hp]; exists p; case: (IHc (p,gi)) => [h1 h2];  intuition.
move => [p hp]; exists p; case: (IHc (p,gi)) => [h1 h2];  intuition.
Qed.
*)

(* two ways to get rid of the (Hol3 P->P) and
  replace it by top3 *)

 Fixpoint trex o :=
  match o with
  | Hol3 P => P
  | impl3 o P =>
      (trex o)
  | impr3 P o => (trex o)
  | orl3 o P => (trex o)
  | orr3 P o =>(trex o)
  | andl3 o P => (trex o)
  | andr3 P o => (trex o)
  | fa3 p =>  forall n,   (trex (p n))
  | ex3 p => forall n, (trex (p n))
  | top3 => True
  | bot3 => False
  end.

 Fixpoint trexe o :=
  match o with
  | Hol3 P => False
  | impl3 o P =>
      (trexe o)
  | impr3 P o => (trexe o)
  | orl3 o P => (trexe o)
  | orr3 P o =>(trexe o)
  | andl3 (Hol3 e) P => e
  | andl3 o P => trexe o
  | andr3 P o => (trexe o)
  | fa3 p =>  forall n,   (trexe (p n))
  | ex3 p => forall n, (trexe (p n))
  | top3 => True
  | bot3 => False
  end.


Fixpoint o3_norm (o:o3) : o3 :=
  match o with
  | Hol3 P => top3
  | impr3 B o => impr3 B (o3_norm o)
  | impl3 o B => impl3 (o3_norm o) B
  | andr3 B o => andr3 B (o3_norm o)
  | andl3 o B => andl3 (o3_norm o) B
  | orr3 B o => orr3 B (o3_norm o)
  | orl3 o B => orl3 (o3_norm o) B
  | fa3 f => fa3 (fun n => o3_norm (f n))
  | ex3 f => ex3 (fun n => o3_norm (f n))
  | x => x
  end.


Fixpoint o3_norme (o:o3) : o3 :=
  match o with
  | Hol3 P => top3
  | impr3 B o => impr3 B (o3_norme o)
  | impl3 o B => impl3 (o3_norme o) B
  | andr3 B o => andr3 B (o3_norme o)
  | andl3 (Hol3 _) B => Hol3 B
  | andl3 o B => andl3 (o3_norme o) B
  | orr3 B o => orr3 B (o3_norme o)
  | orl3 o B => orl3 (o3_norme o) B
  | fa3 f => fa3 (fun n => o3_norme (f n))
  | ex3 f => ex3 (fun n => o3_norme (f n))
  | x => x
  end.

Fixpoint o3_id (o:o3) (Q:Prop) : Type :=
  match o with
  | Hol3 P => P = (Q->Q)
  | impr3 _ o => o3_id o Q
  | impl3 o _ => o3_id o Q
  | andr3 _ o => o3_id o Q
  | andl3 o _ => o3_id o Q
  | orr3 _ o => o3_id o Q
  | orl3 o _ => o3_id o Q
  | fa3 f => forall n,  o3_id (f n) Q
  | ex3 f => forall n,  o3_id (f n) Q
  | top3 => True
  | bot3 => True
  end.

Lemma o3_norm_corr :
  forall Q o, (o3_id o Q) -> (tr3 o)<->(tr3(o3_norm o)).
  move=> Q.
  elim => [P|||o ho B|B o ho|o ho B|B o ho|o ho B|B o ho
          |f hf|f hf]=>/= h; split; auto; first (by rewrite h);
try          move: (ho h) => [h1 h2];
auto; try (by intuition);
try (by move => hn n; case: (hf n); auto);
move => [n hn]; case: (hf n); eauto.
Qed.



Lemma trex_norm_corr : forall o,  (trex o) ->  (tr3 o)<->(tr3(o3_norm o)).
elim => [P|||o ho B|B o ho|o ho B|B o ho|o ho B|B o ho
          |f hf|f hf]=>/= h; split; (try case (ho h) => h1 h2); auto;
          try  tauto;
   try (by move => hn n; case: (hf n); auto);
   move => [n hn]; case: (hf n); eauto.
Qed.


Lemma trex_norme_corr : forall o,  (trexe o) ->  (tr3 o)<->(tr3(o3_norme o)).
elim => [P|||o ho B|B o ho|o ho B|B o ho|o ho B|B o ho
          |f hf|f hf]=>/= h; split; (try case (ho h) => h1 h2); auto;
          try  tauto;
          try (by move => hn n; case: (hf n); auto);
          try (by move: h o; case: B => //=; auto;tauto);
          move => [n hn]; case: (hf n); eauto.
Qed.


Lemma trex_norm_apply : forall o,  (trex o) ->  (trl3(o3_norm o)) -> (tr3 o).
move => o h1 h2; case: (trex_norm_corr o); auto.
Qed.


Lemma trex_norme_apply : forall o,  (trexe o) ->  (trl3(o3_norme o)) -> (tr3 o).
move => o h1 h2; case: (trex_norme_corr o); auto.
Qed.

(* just to illustrate possible use *)


Lemma o3_norm_apply : forall o,
    {Q & o3_id o Q} -> (trl3 (o3_norm o)) -> (tr3 o).
move => o [Q eQ] h; case: (o3_norm_corr Q o); auto.
Qed.

(*
(* with the second version *)

Lemma ex1 : (tr3  (b3 (cons false (cons false nil)) iS 0 fgs I 0 fhs I)).
  apply o3_norm_apply;
    first by simpl; eauto.
  simpl.
Abort.

(* with the first version *)
Lemma ex1 : (tr3  (b3 (cons false (cons false nil)) iS 0 fgs I 0 fhs I)).
apply trex_norm_apply; first done.
simpl.
Abort.

(* beginning : obsolete part *)
(* simplification on o3's - but cannot not erase quantifiers *)
Fixpoint simpl3 (o:o3) : o3 :=
  match o with
  | top3 => top3
  | bot3 => bot3
  | Hol3 A => Hol3 A
  | impr3 B o =>
      match (simpl3 o) with
      | top3 => top3
      | A' => impr3 B A'
      end
  | impl3 o B =>
      match (simpl3 o) with
      | top3 => Hol3 B 
      | bot3 => top3
      | A' => impl3 A' B
      end
  | andr3 B o =>
      match simpl3 o with
      | top3 => Hol3 B 
      | bot3 => bot3
      | A' => andr3 B A'
      end
  | andl3 o B => 
      match simpl3 o with
      | top3 => Hol3 B
      | bot3 => bot3
      | A' => andl3 A' B
      end
  | orr3 B o =>
      match simpl3 o with
      | top3 => top3
      | bot3 => Hol3 B
      | A' => orr3 B A'
      end
  | orl3 o B =>
      match simpl3 o with
      | top3 => top3
      | bot3 => Hol3 B
      | A' => orl3 A' B
      end
  | fa3 f => fa3 (fun n => simpl3 (f n))
  | ex3 f => ex3 (fun n => simpl3 (f n))
  end.
Print o3.
Lemma simpl3_corr : forall o, tr3 o <-> tr3 (simpl3 o).
  elim => [ P |||o [h1 h2] B|B o [h1 h2]|o [h1 h2] B
          |B o [h1 h2]|B o [h1 h2]|o [h1 h2] B|f hf|f hf]  =>//= ; split; auto;

   try (by move:h1 h2; case: simpl3 => //=; intuition).
  move =>hn n. move: (hn n);case: (hf n);auto.
  move =>hn n. move: (hn n);case: (hf n);auto.
move=>[n hn]; exists n;case: (hf n); auto.
move=>[n hn]; exists n;case: (hf n); auto.
Qed.

Lemma simpl3_do1 :
  forall o, tr3 o -> tr3 (simpl3 o).
  by move => o; case:(simpl3_corr o). Qed.
Check b3.

Lemma simpl3_do2 :
  forall o, tr3 (simpl3 o) -> tr3 o.
  by move => o; case:(simpl3_corr o). Qed.



(* with the first version *)
Lemma ex1 : (tr3  (b3 (cons false (cons false nil)) iS 0 fgs I 0 fhs I)).
apply trex_norm_apply; first done.
apply simpl3_do2.
simpl.
Abort.
(* end obsolete part *)
*)


(* Tactics for reification *)

Notation "'subst!' y 'for' x 'in' f" :=
 (match y with x => f end) (at level 10, f at level 200).

Ltac beta1 func arg :=
 lazymatch func with
 | (fun a => ?f) => constr:(subst! arg for a in f)
 end.



Ltac wrap names vals t :=
 lazymatch names with
 | nil => t
 | cons ?y ?ys => constr:(let (v0, rest0) := vals in ltac:(
     let t' := wrap ys rest0 t in
     lazymatch eval pattern y in t' with
     | ?f y => let t'' := beta1 f v0 in exact t''
     end))
 end.



(*
Lemma test_wrap: forall a b c: nat,
   (fun (z: pp 3) => ltac:(
     let r := wrap (cons a (cons b (cons c nil))) z (a + b = c) in
     exact r)) (a, (b, (c, I))) =
   (fun (z: pp 3) => a + b = c) (a, (b, (c, I))).
Proof. intros. simpl. reflexivity. all: fail. Abort.

 *)

Ltac reify_rec l n  env t :=  
  lazymatch constr:(l) with
    | nil => constr:(Hole n (fun (z: pp n) =>
                               ltac:(let r := wrap env z t in exact r)))
  | cons true ?l' =>
      lazymatch t with
      | ?a -> ?b => 
          let ra := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_rec l' n  env b in
          constr:(impr n ra rb) 
    | ?a /\ ?b => 
          let ra := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_rec l' n  env b in
          constr:(andr n ra rb) 
    | ?a \/ ?b => 
          let ra := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_rec l' n  env b in
          constr:(orr n ra rb) 
       end
  | cons false ?l' =>
      lazymatch t with
            | forall x: nat, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: nat => ltac:(
       let body := beta1 body' y in
       let r := reify_rec l' (S n) (cons y env) body in
       exact r))
     with
     | (fun _: nat => ?r) => constr:(fa n r)
     end
      | exists x: nat, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: nat => ltac:(
       let body := beta1 body' y in
       let r := reify_rec l' (S n) (cons y env) body in
       exact r))
     with
     | (fun _: nat => ?r) => constr:(ex n r)
     end   

      | ?a -> ?b => 
          let rb := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_rec l' n  env a in
          constr:(impl n ra rb) 
      | ?a /\ ?b => 
          let rb := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_rec l' n  env a in
          constr:(andl n ra rb) 
      | ?a \/ ?b => 
          let rb := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_rec l' n  env a in
          constr:(orl n ra rb) 
     
        | _ => constr:(Hole n (fun (z: pp n) =>
                               ltac:(let r := wrap env z t in exact r)))
     
end
end.


(* same but detecting True and False *)
Ltac reify_rec_at l n  env t :=  
  lazymatch constr:(l) with
  | nil =>
      match t with
      | True => constr:(cTop n)
      | False => constr:(cBot n)
      | _ =>
          constr:(Hole n (fun (z: pp n) =>
                               ltac:(let r := wrap env z t in exact r)))
      end
  | cons true ?l' =>
      lazymatch t with
      | ?a -> ?b => 
          let ra := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_rec_at l' n  env b in
          constr:(impr n ra rb) 
    | ?a /\ ?b => 
          let ra := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_rec_at l' n  env b in
          constr:(andr n ra rb) 
    | ?a \/ ?b => 
          let ra := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_rec_at l' n  env b in
          constr:(orr n ra rb) 
       end
  | cons false ?l' =>
      lazymatch t with
            | forall x: nat, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: nat => ltac:(
       let body := beta1 body' y in
       let r := reify_rec_at l' (S n) (cons y env) body in
       exact r))
     with
     | (fun _: nat => ?r) => constr:(fa n r)
     end
      | exists x: nat, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: nat => ltac:(
       let body := beta1 body' y in
       let r := reify_rec_at l' (S n) (cons y env) body in
       exact r))
     with
     | (fun _: nat => ?r) => constr:(ex n r)
     end   

      | ?a -> ?b => 
          let rb := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_rec_at l' n  env a in
          constr:(impl n ra rb) 
      | ?a /\ ?b => 
          let rb := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_rec_at l' n  env a in
          constr:(andl n ra rb) 
      | ?a \/ ?b => 
          let rb := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_rec_at l' n  env a in
          constr:(orl n ra rb) 
     
        | _ => constr:(Hole n (fun (z: pp n) =>
                               ltac:(let r := wrap env z t in exact r)))
     
end
  end.




Ltac reify_goal l :=
 lazymatch goal with
 | |- ?g => let r := reify_rec l 0  (@nil nat) g in change (coerce 0 r I)
 end.
  
Ltac reify_goal_at l :=
 lazymatch goal with
 | |- ?g => let r := reify_rec_at l 0  (@nil nat) g in change (coerce 0 r I)
 end.

Ltac reify_hyp l h :=
 move: h => h;
 lazymatch goal with
 | h : ?g |- _ => let r := reify_rec l 0  (@nil nat) g in (change (coerce 0 r I) in h)
 end.


(* Similar but focusing on equalities *)
Ltac reify_eq_rec l n  env t :=  
  lazymatch constr:(l) with
  | nil =>
      lazymatch constr:(t) with
      | (@eq _ ?t1 ?t2) =>
          constr:(equality n ((fun (z: pp n) =>
                                 ltac:(let r := wrap env z t1 in exact r)))
                           ((fun (z: pp n) =>
                                 ltac:(let r := wrap env z t2 in exact r))))
                           
      end
  | cons true ?l' =>
      lazymatch t with
      | ?a -> ?b => 
          let ra := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_eq_rec l' n  env b in
          constr:(impr n ra rb) 
    | ?a /\ ?b => 
          let ra := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_eq_rec l' n  env b in
          constr:(andr n ra rb) 
    | ?a \/ ?b => 
          let ra := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_eq_rec l' n  env b in
          constr:(orr n ra rb) 
       end
  | cons false ?l' =>
      lazymatch t with
      | forall x: nat, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: nat => ltac:(
       let body := beta1 body' y in
       let r := reify_eq_rec l' (S n) (cons y env) body in
       exact r))
     with
     | (fun _: nat => ?r) => constr:(fa n r)
     end
      | exists x: nat, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: nat => ltac:(
       let body := beta1 body' y in
       let r := reify_eq_rec l' (S n) (cons y env) body in
       exact r))
     with
     | (fun _: nat => ?r) => constr:(ex n r)
     end   

      | ?a -> ?b => 
          let rb := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_eq_rec l' n  env a in
          constr:(impl n ra rb) 
      | ?a /\ ?b => 
          let rb := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_eq_rec l' n  env a in
          constr:(andl n ra rb) 
      | ?a \/ ?b => 
          let rb := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_eq_rec l' n  env a in
          constr:(orl n ra rb) 
     
        | _ => constr:(Hole n (fun (z: pp n) =>
                               ltac:(let r := wrap env z t in exact r)))
     
end
  end.


(*
(* TODO : write the same to focus on a term to berepaced by an equality *)


Ltac reify_term_rec l n  env t :=  
  lazymatch constr:(l) with
  | nil =>
      lazymatch constr:(t) with
      | (@eq _ ?t1 ?t2) =>
          constr:(equality n ((fun (z: pp n) =>
                                 ltac:(let r := wrap env z t1 in exact r)))
                           ((fun (z: pp n) =>
                                 ltac:(let r := wrap env z t2 in exact r))))
                           
      end
  | cons true ?l' =>
      lazymatch t with
      | ?a -> ?b => 
          let ra := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_term_rec l' n  env b in
          constr:(impr n ra rb) 
    | ?a /\ ?b => 
          let ra := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_term_rec l' n  env b in
          constr:(andr n ra rb) 
    | ?a \/ ?b => 
          let ra := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_term_rec l' n  env b in
          constr:(orr n ra rb) 
       end
  | cons false ?l' =>
      lazymatch t with
      | forall x: nat, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: nat => ltac:(
       let body := beta1 body' y in
       let r := reify_term_rec l' (S n) (cons y env) body in
       exact r))
     with
     | (fun _: nat => ?r) => constr:(fa n r)
     end
      | exists x: nat, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: nat => ltac:(
       let body := beta1 body' y in
       let r := reify_term_rec l' (S n) (cons y env) body in
       exact r))
     with
     | (fun _: nat => ?r) => constr:(ex n r)
     end   

      | ?a -> ?b => 
          let rb := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_term_rec l' n  env a in
          constr:(impl n ra rb) 
      | ?a /\ ?b => 
          let rb := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_term_rec l' n  env a in
          constr:(andl n ra rb) 
      | ?a \/ ?b => 
          let rb := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_term_rec l' n  env a in
          constr:(orl n ra rb) 
     
        | _ => constr:(Hole n (fun (z: pp n) =>
                               ltac:(let r := wrap env z t in exact r)))
     
end
  end.
*)

(*
Ltac reify_eq_rec l n  env t :=  
  lazymatch constr:(l) with
  | nil =>
      lazymatch constr:(t) with
      | (@eq _ ?t1 ?t2) =>
          constr:(equality n ((fun (z: pp n) =>
                                 ltac:(let r := wrap env z t1 in exact r)))
                           ((fun (z: pp n) =>
                                 ltac:(let r := wrap env z t2 in exact r))))
                           
      end
  | cons true ?l' =>
      lazymatch t with
      | ?a -> ?b => 
          let ra := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_eq_rec l' n  env b in
          constr:(impr n ra rb) 
    | ?a /\ ?b => 
          let ra := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_eq_rec l' n  env b in
          constr:(andr n ra rb) 
    | ?a \/ ?b => 
          let ra := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_eq_rec l' n  env b in
          constr:(orr n ra rb) 
       end
  | cons false ?l' =>
      lazymatch t with
      | forall x: nat, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: nat => ltac:(
       let body := beta1 body' y in
       let r := reify_eq_rec l' (S n) (cons y env) body in
       exact r))
     with
     | (fun _: nat => ?r) => constr:(fa n r)
     end
      | exists x: nat, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: nat => ltac:(
       let body := beta1 body' y in
       let r := reify_eq_rec l' (S n) (cons y env) body in
       exact r))
     with
     | (fun _: nat => ?r) => constr:(ex n r)
     end   

      | ?a -> ?b => 
          let rb := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_eq_rec l' n  env a in
          constr:(impl n ra rb) 
      | ?a /\ ?b => 
          let rb := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_eq_rec l' n  env a in
          constr:(andl n ra rb) 
      | ?a \/ ?b => 
          let rb := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_eq_rec l' n  env a in
          constr:(orl n ra rb) 
     
        | _ => constr:(Hole n (fun (z: pp n) =>
                               ltac:(let r := wrap env z t in exact r)))
     
end
  end.
*)
Ltac reify_goal_eq l :=
 lazymatch goal with
 | |- ?g => let r := reify_eq_rec l 0  (@nil nat) g in change (coerce 0 r I)
 end.
  

Ltac reify_hyp_eq l h :=
 lazymatch goal with
 | h : ?g |- _ => let r := reify_eq_rec l 0  (@nil nat) g in (change (coerce 0 r I) in h)
 end.


Ltac find_path p :=
  lazymatch p with
  | Hol3 _ => constr:(@nil bool)
  | impl3 ?q _ =>  let rq :=(find_path q) in constr:(cons false rq)
  | impr3 _ ?q => let rq := (find_path q) in constr:(cons true rq)
  | orl3 ?q _ => let rq := (find_path q) in constr:(cons false rq)
  | orr3 _ ?q => let rq := (find_path q) in constr:(cons true rq)
  | andl3 ?q _ => let rq := (find_path q) in constr:(cons false rq)
  | andr3 _ ?q => let rq := (find_path q) in constr:(cons true rq)
  | fa3 ?f => let ff:= eval compute in (f 0) in
                let rq := (find_path ff) in constr:(cons false rq)
  | ex3 ?f =>  let ff:= eval compute in (f 0) in
                let rq := (find_path ff) in constr:(cons false rq)
  | _ => constr:(@nil bool)
  end.

(* to go from o3 to cx in order to perform the simplification *)
Ltac rereify_goal :=
  match goal with
  | |- (trl3 ?o) =>
      let r := (find_path constr:(o)) in
      rewrite /trl3 /=; reify_goal_at r
  end.


(* the tactic for backward proof steps *)
Ltac back h hp gp t i :=
  reify_goal gp;
  reify_hyp hp h;
  match goal with
    | h : (coerce 0 ?hc _) |- _ =>
        apply (b3_corr t i 0 I 0 I hc);
        last  assumption;
        unfold coerce in h  ;
        (apply trex_norm_apply; [simpl; try done; auto|
          rewrite /b3 /o3_norm ;
          try exact I; rewrite /= /cT /cB;
          rereify_goal; apply simpl_corr; rewrite /simpl /cT /cB /coerce ?ppce;
        try exact I])
  end. 


Definition empty_inst : inst.
apply nil.
Defined.

(*
Goal ( 2=2 /\ 3=3) -> 2=2 /\ 3=3.
intro xx.

back xx  ((cons false (@nil bool)))
     ((cons false (@nil bool)))
     (cons true (cons false nil)) empty_inst.

back xx  ( (cons false (@nil bool)))  ( ( (@nil bool))) (cons false ( nil)) empty_inst.
Abort.


Definition ex_ex : inst.
unfold inst.
apply cons; last apply nil.
apply Some.
exists 1.
exists 0.
move => [i j] _.
exact i.
Defined.

Definition ex_ex2 : inst.
unfold inst.
apply (cons None).
apply (cons None).
apply nil.
Defined.


Goal (exists x, x=2 /\ 3=3) -> exists y, y=2 /\ 3=3.

move => [x [e _]].
exists x.
change (coerce 0 (equality 0 (fun _ =>  x)(fun _ =>  2)) I) in e.




change (coerce 0
              ( andl 0
               (property 0
                  (fun y: nat*True =>
                     (let (z,_) := y in (x = z)))
                  (fun _ => 
               2) )
               (fun _ => 3=3)) I).


apply (b3_corr (true :: true :: nil)%list empty_inst 0
               I 0 ) with (hyp := (equality 0 (fun _ : pp 0 => x) (fun _ : pp 0 => 2)));
last assumption;
unfold b3;
apply trex_norme_apply; first reflexivity;
  rewrite /o3_norme /trl3 /tr3;
  simpl in e.

Abort.

Definition un_inst : nat -> inst.
move => n.
unfold inst.
apply cons; last apply nil.
apply Some. exists 0; exists 0.
move => _ _; exact n.
Defined.



Definition id_inst : inst.
apply cons;  last apply nil.
apply Some; exists 0; exists 1.  
move =>  _ [n _] ; exact n.
Defined.

Lemma essai : (forall x,   x = 3) -> forall y,  2 = y.
move => e y.
change
  (coerce 0 (property 0
                      (fun c => let (y',_) := c in
                                2=y') (fun _ =>  y)) I).


change (coerce 0
               (fa 0
                   (equality 1
                             (fun c =>  let (x,_) := c in x)
                             (fun _ =>  3)))
               I)
       in e.
(*
apply (b3_corr (cons true (cons false (cons true nil)))
             id_inst 0 I 0 I) with
  (hyp :=(fa 0 (equality 1 (fun c : pp 1 => let (x, _) := c in x) (fun _ : pp 1 => 3)))); last assumption.
rewrite /b3   . apply trex_norme_apply; first reflexivity;
  rewrite /o3_norme /trl3 /tr3.
 *)
Abort. 

Lemma essai : ( forall x,  x = 3) -> forall y,  2 = y.
  move => e.

  reify_hyp_eq   (cons false (@nil bool)) e.
reify_goal_eq(cons false nil).
  
change (coerce 0
               (fa 0
                   (equality 1
                             (fun c =>  let (x,_) := c in x)
                             (fun _ =>  3)))
               I) in e.
change (coerce 0
               (fa 0
                   (property 1
                            
                            (fun c =>  let (x,c') := c in
                                       let (y,_) := c' in x=y)
                            (fun _ =>2)))
               I).



apply (b3_corr (cons true (cons false (cons false nil)))
              (un_inst 2) 0 I 0) with
  (hyp :=  (fa 0 (equality 1 (fun c : pp 1 => let (x, _) := c in x) (fun _ : pp 1 => 3))));last exact e.
simpl.



rewrite /b3 /id_inst /convert /appist /convert /trl3.

apply trex_norme_apply; rewrite /trl3 /=; first done.

Abort.
*)
(*

change (coerce 0
              ( andl 0
               (property 0
                  (fun y: nat*True =>
                     (let (x,_) := y in (x = 2)))
             (fun _ => x) )
               (fun _ => 3=3)) I).


apply (b3_corr (true :: false :: nil)%list empty_inst 0
               I 0 ) with (hyp := (equality 0 (fun _ : pp 0 => x) (fun _ : pp 0 => 2)));
last assumption;
unfold b3;
apply trex_norme_apply; first reflexivity;
rewrite /o3_norme /trl3 /tr3.
simpl.
unfold o3_norm.
rereify_goal.

apply simpl_corr.
simpl.

simpl.
simpl in e.


Check trex_norm_apply.

Print trex.







Eval compute in (trl3
    (b3 (true :: false :: nil)%list empty_inst 0
       (equality 0 (fun _ : pp 0 => x) (fun _ : pp 0 => 2)) I 0
       (andl 0
          (property 0 (fun y : nat * True => let (x, _) := y in x = 2) (fun _ : pp 0 => x))
          (fun _ : pp 0 => 3 = 3)) I)).

Check (b3_corr (cons true (cons true  nil)) ( empty_inst)
        0 I 0 I (equality 0 (fun _ : pp 0 => x) (fun _ : pp 0 => 2))
        
        (andl 0 (property 0
                  (fun y: nat*True =>
                     (let (x,_) := y in (x = 2)))
             (fun _ => x) ) (fun _ : pp 0 => 3 = 3))
      ).

Eval compute in 
         (trl3
         (b3 (true :: false :: nil)%list empty_inst 0
            (equality 0 (fun _ : pp 0 => x) (fun _ : pp 0 => 2)) I 0
            (andl 0
               (property 0 (fun y : nat * True => let (x, _) := y in x = 2)
                  (fun _ : pp 0 => x)) (fun _ : pp 0 => 3 = 3)) I) ->
       coerce 0 (equality 0 (fun _ : pp 0 => x) (fun _ : pp 0 => 2)) I ->
       coerce 0
         (andl 0
            (property 0 (fun y : nat * True => let (x, _) := y in x = 2) (fun _ : pp 0 => x))
            (fun _ : pp 0 => 3 = 3)) I).
Eval compute in
  (b3 (cons true (cons true  nil)) ( empty_inst)
        0 (equality 0 (fun _ : pp 0 => x) (fun _ : pp 0 => 2))
        I 0
        (andl 0 (property 0
                  (fun y: nat*True =>
                     (let (x,_) := y in (x = 2)))
             (fun _ => x) ) (fun _ : pp 0 => 3 = 3))
        I ).

Eval compute in
  (b3 ( (cons true  nil)) ( empty_inst)
        0 (equality 0 (fun _ : pp 0 => x) (fun _ : pp 0 => 2))
        I 0
        (property 0
                  (fun y: nat*True =>
                     (let (x,_) := y in (x = 2)))
             (fun _ => x) )
        I ).



  intro xx.

  
  back xx  ( cons false (cons false (@nil bool)))  (cons false (cons false (@nil bool)))
       (cons false (cons false (cons true (cons true  nil)))) ex_ex.

  back xx  ( cons false (cons true (@nil bool)))  (cons false ( (@nil bool)))
       (cons false (cons false (cons true (  nil)))) empty_inst.
Abort. *)

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

