From mathcomp Require Import ssreflect ssreflect.seq.


Definition ls := seq Type.
Notation lsar := (@cons Type nat (@cons Type bool nil)).


Fixpoint sl (l:ls)(n:nat){struct l} : Type :=
  match l,n with
  | nil, _ => unit
  | cons s _, 0 => s
  | cons _ l, S n => sl l n
  end.

Definition arity := ((list nat) * nat)%type.
Definition op_arity := (cons 0 (cons 0 nil),0).


(* tuples of objects *)
Fixpoint ppp (ts : ls)(l : list nat) : Type :=
  match l with
  | nil => unit
  | cons n l =>  ((sl ts n) * (ppp ts l))%type
  end.


Fixpoint ta (ts : ls)(la : list nat)(c : nat) : Type :=
  match la with
  | nil => (sl ts c)
  | cons t0 la => (sl ts t0) -> ta ts la c
  end.

Fixpoint predt  (ts : ls)(la : list nat) : Type :=
  match la with
  | nil => Prop
  | cons t0 la => (sl ts t0) -> predt ts la
  end.

Definition taa ts (a : arity) :=
  let (lt,c) := a in
  ta ts lt c.

(*
Definition predt ts (l : list nat) :=
  (ppp ts l) -> Prop.
*)
Definition cst ts := {t : arity & (taa ts t)}.
Definition p_op : (cst lsar).
exists op_arity.
exact Nat.add.
Defined.

Definition m_op : (cst lsar).
exists op_arity.
exact Nat.mul.
Defined.

Definition pst ts := {a : (list nat) & (predt ts a)}.
Definition eq_arity : pst lsar.
exists (cons 0 (cons 0 nil)).
exact (@eq nat).
Defined.

Definition FOsign :=
  {ts : ls & (list (cst ts) * (list (pst ts)))%type}.

(* ce qui est donné *)
Definition sfo : FOsign.
exists lsar.
split.
exact (cons p_op (cons m_op nil)).
exact (cons eq_arity nil).
Defined.

Definition ts :=  let (ts, _) := sfo in ts.
Definition sort n :=  (sl ts n).


(* elements par défaut *)
Definition def : forall n, sort n.
case => [|[|n]].
exact 99.
exact false.
exact tt.
Defined.


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

Definition trs s1 s2:  sort s1 -> sort s2.
  case e: (eqnqtdec s1 s2) => [s12|s12].
rewrite s12 => v; exact v.
move => _ ; apply def.
Defined.


Lemma trs_corr : forall s v, trs s s v = v.
  move => s v; rewrite /trs /protect_term .
by rewrite  eqnqtdec_refl.
Qed.

Definition pp := (ppp ts).
Check nth.


Definition nthc (c:seq nat)(p : pp c)(n:nat): (sort (nth 0 c n)).
move: n p.
elim: c => [| t c rc][|n]/=.  
- move => _ ; apply def.
- move => _ ; apply def.
- move => [x _]; exact x.
- move => [_ x]; exact (rc n x).
Defined.




(* focused propositions with n free variables *)
Inductive cx : (seq nat)  -> Type :=
| cTop : forall n,  cx n
| cBot : forall n,  cx n
| Hole : forall n,  ((pp n) -> Prop) -> (cx n)
| impr : forall n, ((pp n) -> Prop) -> (cx n) -> (cx n)
| impl : forall n, (cx n) -> ((pp n) -> Prop) -> (cx n)
| orr : forall n, ((pp n) -> Prop) -> (cx n) -> (cx n)
| orl : forall n, (cx n) -> ((pp n) -> Prop) -> (cx n)
| andr : forall n, ((pp n) -> Prop) -> (cx n) -> (cx n)
| andl : forall n, (cx n) -> ((pp n) -> Prop) -> (cx n)
| fa : forall n s, cx (cons s n) -> cx n
| ex : forall n s, cx (cons s n) -> cx n
| equality : forall n s,
    ((pp n) -> (sort s)) ->((pp n) -> (sort s)) -> cx n
| property  : forall n s,
    ((pp (cons s n)) -> Prop) ->
    ((pp n) -> (sort s))  -> cx n.


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
| Hole _ P => P
| impl _ c P => fun x => ((coerce _ c x)  -> (P x))
| impr _ P c => fun x =>  (P x) -> (coerce _ c x)
| orl _ c P => fun x => (coerce _ c x)\/(P x)
| orr _ P c => fun x =>  (P x) \/ (coerce _ c x)
| andl _ c P => fun x => (coerce _ c x) /\ (P x)
| andr _ P c => fun x =>  (P x) /\ (coerce _ c x)
| fa _ s c => fun  x =>  forall p:_, (coerce _ c (p, x))
| ex _ s c => fun  x =>  exists p:_,  (coerce _ c (p, x))
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
      
  | n, fa n' s A =>
      match (cT (cons s n') (simpl (cons s n') A)) with
      | true => cTop  n'
      | _ => fa n' s (simpl (cons s n') A)
      end
  | n, ex n' s A =>
      match (cB (cons s n') (simpl (cons s n') A)) with
      | true => cBot n'
      | _ => ex n' s (simpl (cons s n') A)
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
        [n|n|n P|n A B hB|n A hA B|n A  B hB|n A hA  B
        |n A B hB|n A hA B|n s A hA |n s A hA|n t u|n P t] i //=;
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

(* will indicate which deep operations to perform *)
Definition trace := (list bool).

Fixpoint defs l : pp l :=
  match l with
  | nil => tt
  | cons n l => (def n, defs l)
  end.


(* to avoid problems with type dependency *)

Fixpoint convert n m (i: pp n) : pp m :=
  match n, i, m with
  | nil, tt, m => (defs m)
  | cons s n, i, nil => (defs nil)
  | cons s1 n, (x,i), cons s2 m => (trs s1 s2 x, (convert n m i))
  end.


Lemma convert_corr : forall l i,  convert l l i = i.
  elim => [[]|x l hl[a b]]//=.
  by rewrite trs_corr hl.
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
| fa3 : forall s, (sort s -> o3) -> o3
| ex3 : forall s,  (sort s -> o3) -> o3.

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
  | fa3 s p =>  forall n,   (tr3 (p n))
  | ex3 s p => exists n, (tr3 (p n))
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

Definition ct := seq nat.

Definition inst  :=
  list
    (option
       {s & {n1 : ct & {n2 : ct & (pp n1)->(pp n2) -> sort s}}}).

(* using an inst *)

Definition env := forall s, nat -> sort s.

Definition inst1 := {s : nat & env -> env -> sort s}.


(*
  aenv1 = [(x : nat); (a : bool); (y : nat)]
  aenv2 = [(z : bool); (y : nat)]
  [env1][env2] x + y

  is compiled into:

  fun env1 env2 =>
    add (env1 (sort_index (type_of x aenv1)) (var_index x aenv1))
        (env2 (sort_index (type_of y aenv2)) (var_index y aenv2))
  
  which simplifies (ML computaMLtion) to:

  fun env1 env2 =>
    add (env1 (sort_index "nat") 0)
        (env2 (sort_index "nat") 2)

  which simplifies (ML computation) to:

  fun env1 env2 =>
    add (env1 0 0)
        (env2 0 2)
*)

Definition trad1 : forall n, pp n -> env :=
  fun n p s i =>
    trs (nth 0 n i) s
        (nthc n p i).


Definition trad :
  inst1 -> ct -> ct ->
  {s & {n1 : ct & {n2 : ct & (pp n1)->(pp n2) -> sort s}}}.
move => [s f] n1 n2.
exists s; exists n1; exists n2.
move => p1 p2.
exact (f (trad1 n1 p1)(trad1 n2 p2)). 
Defined.

Definition inst' := list (option inst1).



Definition appist1 sr
           (f:{s : nat &
                     {n1 : _ &
                             {n2 : _ & (pp n1)->(pp n2) -> sort s}}})
           n1 (i1 : pp n1) n2 (i2 : pp n2) :=
  match f with
    existT  s (existT  m1 (existT  m2 f)) =>
      trs s sr (f (convert n1 m1 i1)(convert n2 m2 i2))
  end.

Definition appist sr (g: inst1) n1 c1 n2 c2 :=
  match g with
    existT s f => trs s sr (f (trad1 n1 c1)(trad1 n2 c2))
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
(* "side conditions" are generated (which are actually in the center
   and not on the side : 
    - A->B  for the focused formulas (meant to be A->A in practice)
    - two equalites for equality rewrites which should be two trivial
      reflexive equalities
 *)


Fixpoint b3 (l:trace)(ist:inst')(nh:ct)(hyp : cx nh)(hi : pp nh)
         (ng : ct)(goal : cx ng)(gi : pp ng) : o3 :=
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
      | (property ng' s P v) =>
          match hyp with
          | (equality nh' s' t u) =>
              andl3  
                (Hol3 (s = s'/\((u (convert nh nh' hi))
                       =(trs s s' (v (convert ng ng' gi))))))
                (P (trs s' s (t (convert nh nh' hi)),
                     (convert ng ng' gi)))
          | _ => bot3
          end

      | (impl ng' h B) =>
          (impl3 (f3 l ist nh hyp hi ng' h (convert ng ng' gi))
                 (B (convert ng ng' gi)))

      | (impr ng'  B g) =>
          (impr3 (B (convert ng ng' gi))
                 (b3 l ist nh hyp hi ng' g (convert ng ng' gi)))
      | orl ng' g B =>
          orl3 (b3 l ist nh hyp hi ng' g (convert ng ng' gi))
               (B (convert ng ng' gi))
      | orr ng' B g =>
          orr3  (B (convert ng ng' gi))
                (b3 l ist nh hyp hi ng' g (convert ng ng' gi))
      | andl ng' g B =>
          andl3 (b3 l ist nh hyp hi ng' g (convert ng ng' gi))
               (B (convert ng ng' gi))
      | andr ng' B g =>
          andr3  (B (convert ng ng' gi))
                 (b3 l ist nh hyp hi ng' g (convert ng ng' gi)) 
      |  (fa ng' s g) =>
               fa3 s (fun n=>
                  (b3 l ist nh hyp hi (cons s ng') g
                      (n, convert ng ng' gi))) 
      | ex ng' s g =>
          match ist with
          | cons (Some f) ist =>
              b3 l ist
                 nh hyp hi
                 (cons s ng') g
                 (appist s f nh hi ng gi,
                   (convert ng ng' gi))
          |  cons None ist =>
               ex3 s
                 (fun p =>
                    b3 l ist nh hyp hi
                       (cons s ng') g
                       (p, convert ng ng' gi))
          | nil => bot3
          end  
                
      | cTop _ => top3
                     
      | cBot _ => bot3  
      | Hole _ _ => bot3
      | _ => bot3
      end
  | (cons false l) =>
      match hyp with
          | (equality nh' s t u) =>
              match goal with
              | (property ng' s' P v) =>
                  andl3
                    (Hol3
                    (s=s' /\ ((t (convert nh nh' hi))
                     =(trs s' s (v (convert ng ng' gi))))))
                    (P ((trs s s' (u (convert nh nh' hi))),
                         (convert ng ng' gi)))
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
                (coerce ng goal gi))
      | orr nh' B h =>
          andr3 ((B (convert nh nh' hi))->
                (coerce ng goal gi))
               (b3 l ist nh' h (convert nh nh' hi)
                   ng goal gi) 
      | impr nh' B h =>
          andr3 (B (convert nh nh' hi))
                (b3 l ist nh' h (convert nh nh' hi)
                   ng goal gi)
      | fa n s h =>
          match ist with
          | cons (Some f) ist =>
              (b3 l ist
                  (cons s n) h (convert
                         (cons s nh) (cons s n)
                         ((appist s f nh hi ng gi),hi))
                  ng goal gi)
          | cons None ist =>
              ex3 s
                  (fun p =>
                     (b3 l ist
                         (cons s n) h
                         (convert (cons s nh)(cons s n)
                                  (p, hi))
                         ng goal gi))
          | _ => bot3
          end
      | ex n s h =>
          fa3 s
            (fun p =>
               (b3 l ist
                   (cons s n) h
                   (convert (cons s nh)(cons s n)
                            (p, hi))
                   ng goal gi))
      | impl  _ _ _  => bot3
      | cTop _ => bot3
      | cBot _ => top3
      | Hole _ _ => bot3
      | _ => bot3
      end
  end
with f3 (l:trace)(ist: inst')(n1:ct)(h1 : cx n1)(i1 : pp n1)
        (n2 : ct)(h2 : cx n2)(i2 : pp n2) :
      o3 :=
  match l with
  | nil => top3
  | cons false l =>
      match h1 with
      | equality n1' s1 t u =>
          match h2 with
          | property n2' s2 P v =>
              Hol3 (s1 = s2 ->
                ((v (convert n2 n2' i2)  =
                    (trs s1 s2 (u (convert n1 n1' i1)))
                ->
                  P (convert (cons s2 n2)(cons s2 n2')
                             ((trs s1 s2 (t (convert n1 n1' i1))),
                               i2)))))
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
          impl3 (b3 l ist n2 h2 i2 n1' h1'
                    (convert n1 n1' i1))
                (B (convert n1 n1' i1))
      | impr n1' B h1' =>
          impr3  (B (convert n1 n1' i1))
                 (f3 l ist n1' h1' (convert n1 n1' i1) n2 h2 i2)
      | fa n1' s1 h1' =>
          fa3 s1 (fun n =>
                    (f3 l ist (cons s1 n1') h1'
                        (convert (cons s1 n1)(cons s1 n1') (n, i1))
                          n2 h2 i2)) 
          
      | _ => top3
      end
   | cons true l =>
       match h2 with
                     
       | property n2' s2 P v =>
           match h1 with
          | equality n1' s1 t u =>
              Hol3  (s1=s2 -> 
                     ((v (convert n2 n2' i2)=
                         (trs s1 s2 (t (convert n1 n1' i1))))->
                 P (convert (cons s2 n2)(cons s2 n2')
                            ((trs s1 s2 (u (convert n1 n1' i1))),
                              i2))))
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
          impl3 (b3 l ist n1 h1 i1 n2' h2' (convert n2 n2' i2))
                (B (convert n2 n2' i2))
      | impr n2' B h2' =>
          impr3  (B (convert n2 n2' i2))
                 (f3 l ist n1 h1 i1 n2' h2' (convert n2 n2' i2) )
      | fa n2' s2 h2' =>
          fa3 s2 (fun n =>
                 (f3 l ist n2 h2 i2
                     (cons s2 n2') h2'
                     (convert (cons s2 n2)(cons s2 n2') (n, i2))
                 )) 
          
      | _ => top3
      end
  end   .



(* The main lemma *)
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

- move => _ 
   [|s2 n2]
   [nh'|nh'|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
       |nh' P h|nh' h P|s' nh' h|s' nh' h|nh' t u|nh P v]//= hi
   [|sg ng]
   [ng'|ng'|ng' Q|ng' Q g|ng' g Q|ng' Q g|ng' g Q
       |ng' Q g|ng' g Q|sg' ng' g|sg' ng' g|ng' t' u'|ng' P' v']
   gi //=;
  rewrite /= ?convert_corr ?ppce//=; move => [-> h2] e//=.
- move => ist nh hyp hi ng
          [ng'|ng'|ng' Q|ng' Q g|ng' g Q|ng' Q g|ng' g Q
              |ng' Q g|ng' g Q|ng' sg' g|ng' sg' g
              |ng' sg' t u|ng' s P v] gi //=;
  rewrite /= ?ppce ?convert_corr //=; eauto;
  try (by move => [h|h]; eauto);
  try (by  move => [h1 h2]; split ; eauto).
  * case: ist => [//=|[f|] ist]; first by eauto.
    by move => [w hw]; eauto.
  * induction hyp; rewrite //= convert_corr.
    move => [[ss e] p] tt.
    move: v  s1 s2 e tt p.
    by rewrite -ss => v t t0; rewrite !trs_corr => -> ->.
- move => ist n1 h1 i1 n2 h2 i2 hr1 hr2.
  move: h2 i2 hr2 =>
        [nh'|nh'|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
        |nh' P h|nh' h P|nh' s h|nh' s h|nh' s t u
        |nh' s P v] //=P2 i2;
      rewrite ?convert_corr; eauto;
   try (by case: i2; eauto).
  move: P2 i2 hr1 => i2 pv.
  induction h1; try done; rewrite /= convert_corr.
  move: P v pv s1 s2; case: s; case: s0; try done;
  rewrite /trs ?convert_corr ?eqnqtdec_refl; auto.
      by   move => P v pv t t' <- _ <-.
  move => m1 m2 P v p s1 s2 -> [mm].
  by move : s1 s2; rewrite mm {m1 mm} eqnqtdec_refl /= => w s2 <-.
- move => ist nh
          [nh'|nh'|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
              |nh' P h|nh' h P|nh' s h|nh' s h|nh' s t u
              |nh' s P v] i1 //=;
   rewrite ?convert_corr ?ppce  ?trs_corr //= => ng goal gi;
   try (by intuition; eauto).

case: ist => [//=|[f|] ist]; first by eauto.
  move => [p hp]; eauto.
  move => hh [w hw]; apply (hl1 ist (s::nh') h (w,i1)); eauto.
     by move: (hh w); rewrite trs_corr.

   induction goal; try done; move => /= [[e h2] h3] h4.
  move: P s1 h2 h3 h4 ; rewrite -e ?trs_corr => P t0.
  rewrite trs_corr convert_corr => <- p -> //=.
- move => ist n1
          [nh'|nh'|nh' P|nh' P h|nh' h P|nh' P h
              |nh' h P|nh' P h|nh' h P|nh' s h|nh' s h
              |nh' s t u|nh' s P v] /= 
         i1 n2 h2 i2 p1 p2 //=;
  rewrite ?convert_corr; try (by intuition; eauto).
  induction h2; try done; move => /= ss; move: P s1 p2.
  rewrite -ss; move: {ss} t u p1; case: s;
  rewrite /trs /= ?trs_corr convert_corr ?eqnqtdec_refl;
    first by move =>t u -> P t0 h <-.
  by move => m t u ->P s1 h;
  rewrite ?eqnqtdec_refl /eq_rect_r /= => <-.
Qed.



Definition trl3 := nosimpl tr3.


(* The two practical corollaries *)
Lemma b3_corr :  forall l : trace,
    (forall (ist : inst') (nh : ct)  (hi : pp nh)
            (ng : ct) (gi : pp ng)
            (hyp : cx nh)(goal : cx ng),
        trl3 (b3 l ist nh hyp hi ng goal gi) ->
        coerce nh hyp hi -> coerce ng goal gi).
move => l ist nh hi ng gi hyp goal.  
case: (bf3_corr l) => [h _]; apply h.
Qed.

Lemma f3_corr :
  forall l (ist : inst') (n1 : ct) (h1 : cx n1) (i1 : pp n1) 
         (n2 : ct) (h2 : cx n2) (i2 : pp n2),
    coerce n1 h1 i1 ->
    coerce n2 h2 i2 ->
    trl3 (f3 l ist n1 h1 i1 n2 h2 i2).
move => l ist n1 h1 i1 n2 h2 i2.
case: (bf3_corr l) => [_ h]; apply h.
Qed.
  

(* Socrates example *)
Parameter H M : nat -> Prop.

Definition hm := forall x,  H x -> M x.
Definition hs := H 0.

Definition gs := M 0.

Definition fhs := Hole (nil)  (fun _ => gs).
(*
Definition fgs := fa nil cnat (impr (cons cnat nil)
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
  | fa3 s p =>  forall n,   (trex (p n))
  | ex3 s p => forall n, (trex (p n))
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
  | fa3 s p =>  forall n,   (trexe (p n))
  | ex3 s p => forall n, (trexe (p n))
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
  | fa3 s f => fa3 s (fun n => o3_norm (f n))
  | ex3 s f => ex3 s (fun n => o3_norm (f n))
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
  | fa3 s f => fa3 s (fun n => o3_norme (f n))
  | ex3 s f => ex3 s (fun n => o3_norme (f n))
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
  | fa3 s f => forall n,  o3_id (f n) Q
  | ex3 s f => forall n,  o3_id (f n) Q
  | top3 => True
  | bot3 => True
  end.

Lemma o3_norm_corr :
  forall Q o, (o3_id o Q) -> (tr3 o)<->(tr3(o3_norm o)).
  move=> Q.
  elim => [P|||o ho B|B o ho|o ho B|B o ho|o ho B|B o ho
          |s f hf|s f hf]=>/= h; split; auto; first (by rewrite h);
try          move: (ho h) => [h1 h2];
auto; try (by intuition);
try (by move => hn n; case: (hf n); auto);
move => [n hn]; case: (hf n); eauto.
Qed.



Lemma trex_norm_corr : forall o, (trex o) ->
                                 (tr3 o)<->(tr3(o3_norm o)).
elim => [P|||o ho B|B o ho|o ho B|B o ho|o ho B|B o ho
        |s f hf|s f hf]=>/= h; split;
        (try case (ho h) => h1 h2); auto;
        try  tauto;
        try (by move => hn n; case: (hf n); auto);
        move => [n hn]; case: (hf n); eauto.
Qed.


Lemma trex_norme_corr :
  forall o, (trexe o) -> (tr3 o)<->(tr3(o3_norme o)).
Proof.
elim => [P|||o ho B|B o ho|o ho B|B o ho|o ho B|B o ho
        |s f hf|s f hf]=>/= h; split;
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
(*
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
 | cons (existT _ ?UU ?y) ?ys =>
     constr:(
       let (v0, rest0) := vals
       in ltac:(
            let t' := wrap ys rest0 t in
            lazymatch eval pattern y in t' with
            | ?f y => let t'' := beta1 f v0 in exact t''
                        end))
 end.

(*
Ltac wrap names vals t :=
 lazymatch names with
 | nil => t
 | cons ?y ?ys =>
     constr:(
       let (v0, rest0) := vals
       in ltac:(
            let t' := wrap ys rest0 t in
            lazymatch eval pattern y in t' with
            | ?f y => let t'' := beta1 f v0 in exact t''
                        end))
 end.

*)

Fixpoint ncnat n :=
  match n with
  |0 => nil
  |S n => cons 1 (ncnat n)
  end.

Notation ww x := (@existT Type (fun x=>x) nat x).

Lemma test_wrap: forall a b c: nat,
    (fun (z: nat*(nat*(nat*True))) =>
       ltac:(
               let r := (wrap
                          (cons (ww a) (cons (ww b) (cons (ww c) nil)))
                          z
                          (a + b = c)) in
     exact r)) (a, (b, (c, I))) =
   (fun (z: nat*(nat*(nat*True))) => a + b = c) (a, (b, (c, I))).
Proof. intros. simpl. reflexivity. all: fail. Abort. 
(*
Lemma test_wrap: forall a b c: nat,
   (fun (z: pp (ncnat 3)) => ltac:(
     let r := wrap (cons a (cons b (cons c nil))) z (a + b = c) in
     exact r)) (a, (b, (c, I))) =
   (fun (z: pp (ncnat 3)) => a + b = c) (a, (b, (c, I))).
Proof. intros. simpl. reflexivity. all: fail. Abort.



Fixpoint ncnat n :=
  match n with
  |0 => nil
  |S n => cons 0 (ncnat n)
  end.

*)

Ltac st_aux n l T :=
  let U := eval compute in T in
    let m := eval compute in l in
  lazymatch constr:(m) with
  | cons  U ?y  => constr:(n)
  | cons  _ ?l1  => st_aux constr:(S n) l1 T
  | nil => constr:(999)
  end.

Ltac tst T := (st_aux constr:(0) constr:(lsar) T).  

Definition dyn := {T:Type & T}.

(*
Set Printing All.
Print dyn.
Print sigT.
istT : forall (x : A) (_ : P x), @sigT A P.
*)

Ltac reify_rec l n env t :=  
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
       | forall x: (sort ?s), @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: (sort s) => ltac:(
           let body := beta1 body' y in
              let r := reify_rec l' (cons s n) (cons (@existT Type (fun x => x) (sort s) y) env) body in
              exact r))
     with
     | (fun _: (sort s) => ?r) => constr:(fa n s r) 
     end

      | ?a -> ?b => 
          let rb :=
            constr:(fun (z: pp n) =>
              ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_rec l' n  env a in
          constr:(impl n ra rb) 
      | forall x: ?T, @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: T => ltac:(
           let body := beta1 body' y in
           let s := ltac:(tst T) in                                  
              let r := reify_rec l' (cons s n) (cons (@existT Type (fun x => x) T y) env) body in
              exact r))
     with
     | (fun _: T => ?r) => constr:(fa n ltac:(let s := tst T in exact s) r) 
     end
      | exists x: ?T, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: T => ltac:(
          let body := beta1 body' y in
          let s := ltac:(tst T) in
       let r := reify_rec l' (cons
                               s
                               n) (cons  (@existT Type (fun x => x) T y) env) body in
       exact r))
     with
     | (fun _: T => ?r) => constr:(ex n
                                      ltac:(let s := tst T in exact s) r)
     end   
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

Ltac reify_rec_at l n env t :=  
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

       | forall x: (sort ?s), @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: (sort s) => ltac:(
           let body := beta1 body' y in
              let r := reify_rec_at l' (cons s n) (cons (@existT Type (fun x => x) (sort s) y) env) body in
              exact r))
     with
     | (fun _: (sort s) => ?r) => constr:(fa n s r) 
     end
        
      | ?a -> ?b => 
          let rb := constr:(fun (z: pp n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_rec_at l' n  env a in
          constr:(impl n ra rb) 
      | forall x: ?T, @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: T => ltac:(
           let body := beta1 body' y in
           let s := ltac:(tst T) in                                  
              let r := reify_rec_at l' (cons s n) (cons (@existT Type (fun x => x) T y) env) body in
              exact r))
     with
     | (fun _: T => ?r) => constr:(fa n ltac:(let s := tst T in exact s) r) 
     end
      | exists x: ?T, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: T => ltac:(
          let body := beta1 body' y in
           let s := ltac:(tst T) in                         let r := reify_rec_at l' (cons
                               s
                               n) (cons  (@existT Type (fun x => x) T y) env) body in
       exact r))
     with
     | (fun _: T => ?r) => constr:(ex n
                                      ltac:(let s := tst T in exact s)
                                             r)
     end   
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

(*
Ltac reify_rec_at l n env t :=  
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
      | forall x: ?T, @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: T => ltac:(
           let body := beta1 body' y in
           let s := ltac:(tst T) in                                  
              let r := reify_rec_at l' (cons s n) (cons y env) body in
              exact r))
     with
     | (fun _: T => ?r) => constr:(fa n ltac:(let s := tst T in exact s) r) 
     end
      | exists x: ?T, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: T => ltac:(
          let body := beta1 body' y in
          let s := ltac:(let s:= tst T in exact s) in
       let r := reify_rec_at l' (cons
                               s
                               n) (cons y env) body in
       exact r))
     with
     | (fun _: T => ?r) => constr:(ex n
                                      ltac:(let s := tst T in exact s)
                                             r)
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

Check coerce.
*)
Ltac reify_goal l :=
 lazymatch goal with
 | |- ?g =>
     let r := reify_rec l  (@nil nat)  (@nil dyn)  g in
     change (coerce (@nil nat) r tt)
 end.


Ltac reify_goal_at l :=
 lazymatch goal with
 | |- ?g =>
     let r := reify_rec_at l (@nil nat)  (@nil dyn) g in change (coerce (@nil nat) r tt)
 end.

Ltac reify_hyp l h :=
  move: h => h;
 lazymatch goal with
 | h : ?g |- _ =>
     let r := reify_rec l (@nil nat)  (@nil dyn) g in (change (coerce (@nil nat) r tt) in h)
 end.

Ltac reify_hyp_at l h :=
 lazymatch goal with
 | h : ?g |- _ =>
     let r := reify_rec_at l (@nil nat)  (@nil dyn) g in (change (coerce (@nil nat) r tt) in h)
 end.
  


(* Once a back or forward steps is performed, we want to apply simplification
   (simpl function).
  For that we need to translate the o3 back into a cx *)

(* this finds the path to the focused location *)
Ltac find_path p :=
  lazymatch p with
  | Hol3 _ => constr:(@nil bool)
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
Ltac rereify_goal :=
  match goal with
  | |- (trl3 ?o) =>
      let r := (find_path constr:(o)) in
      rewrite /trl3 /=; reify_goal_at r
  end.

Ltac rereify_hyp h :=
  match goal with
  | h : (trl3 ?o) |- _ =>
        let r := (find_path constr:(o)) in
      rewrite /trl3 /= in h; reify_hyp_at r h
  end.


Ltac back h hp gp t i :=
  let h' := fresh h in
  move:(h) => h';
  reify_goal gp;
  reify_hyp hp h';
  match goal with
    | h' : (coerce (@nil nat) ?hc _) |- _ =>
        apply (b3_corr t i (@nil nat) tt (@nil nat) tt hc);
last  assumption;
        clear h'  ;
        (apply trex_norm_apply; [simpl; try done; auto|
          rewrite /b3 /o3_norm ;
          try exact tt; rewrite /= /cT /cB ;
          rereify_goal; apply simpl_corr; rewrite /simpl /cT /cB /coerce ?ppce;
          try exact tt ]);
  rewrite /trs /sl /ts /sfo ?eqnqtdec_refl /eq_rect_r /eq_rect /Logic.eq_sym;
  try by apply I
  end. 



Ltac forward h1 h2 h3 hp1 hp2 t i :=
  let h1' := fresh h1 in
  let h2' := fresh h2 in
  move: (h1) => h1';
  move: (h2) => h2';
  reify_hyp hp1 h1';
  reify_hyp hp2 h2';
  match goal with
  |  h1' : (coerce (@nil nat) ?hc1 _) ,
     h2' : (coerce (@nil nat) ?hc2 _) |- _  =>
           move:
           (f3_corr t i (@nil nat) hc1 tt
                    (@nil nat) hc2 tt h1' h2') => h3
  end;
  clear h1' h2';
    apply trex_norm_fapply in h3;
  [ | simpl; try done; auto];
  rewrite /f3 /o3_norm /= /cT /cB in h3;
    match goal with
  | h3 : (trl3 ?o) |- _ =>
      let p := (find_path o) in
      rewrite /trl3 /= in h3 ;
      match goal with
        | h3 : ?dh |- _ =>
            let r := reify_rec_at p (@nil nat)  (@nil dyn) dh in
move: (simpl_fstep (@nil nat) r tt h3) => {h3} h3; simpl in h3 end end.



Definition empty : inst'.
apply nil.
Defined.

Parameter A B C D : Prop.

Goal (A -> B) ->(B/\A) ->  B /\ A.
  intros b c.


  forward c b d   (cons true nil) (cons false nil) (cons true (cons false nil)) empty.
Abort.


Definition ii : inst'.
apply cons.
2 : apply nil.
apply Some.
unfold inst1.
exists 1.
unfold env.
intros e1 e2.
apply e1.
apply 0.
Defined.

(*
apply cons.
2 : apply nil.
apply Some.
exists 1.
exists (cons 1 (cons 0 nil)).
exists nil.
rewrite /pp /ppp /=.
move => [x _] _ ; exact x.
Defined.
*)

Goal (forall z:bool, true=z) -> forall x:bool,forall y,(true=x \/ y=2).
  intros h.


  
  back h (cons false nil) (cons false (cons false (cons false nil))) (cons true (cons true (cons false (cons true nil)))) ii.
Abort.





(* Similar but focusing on equalities *)
(* probably needs to be debugged *)
(*
Ltac reify_eq_rec l n  env t :=  
  lazymatch constr:(l) with
  | nil =>
      lazymatch constr:(t) with
      | (@eq ?T ?t1 ?t2) =>
          ltac:(let s := tst T in 
          
          constr:(equality n s
                                    ((fun (z: pp n) =>
                                 ltac:(let r := wrap env z t1 in exact r)))
                           ((fun (z: pp n) =>
                                 ltac:(let r := wrap env z t2 in exact r)))))
                           
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
      | forall x: ?T, @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: T =>
                              ltac:(let body := beta1 body' y in
                                    let s:= (st T) in
                  let r := reify_eq_rec l' (cons s n)
                                        (cons y env) body in
            exact r))
            with
            | (fun _: _ => ?r) => constr:(fa n ltac:(let s:= (st T) in exact s) r)
          end
      | exists x: ?T, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: T => ltac:(
          let body := beta1 body' y in
          let r := reify_eq_rec l' (cons
                                      ltac:(let s := tst T in exact s)
                                             n) (cons y env) body in
            exact r))
           with
          | (fun _: _ => ?r) => constr:(ex n T r)
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

(*
(* TODO : write the same to focus on a term to be replaced by an equality *)


Ltac reify_term_rec l n  env t :=  
  lazymatch constr:(l) with
  | nil =>
      lazymatch constr:(t) with
      | (@eq _ ?t1 ?t2) =>
          constr:(equality n (st T) ((fun (z: pp n) =>
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
      | forall x: ?T, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: T => ltac:(
       let body := beta1 body' y in
       let r := reify_eq_rec l' (cons ltac:(st T) n) (cons y env) body in
       exact r))
     with
     | (fun _: nat => ?r) => constr:(fa n ltac:(st T) r)
     end
      | exists x: ?T, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: T => ltac:(
       let body := beta1 body' y in
       let r := reify_eq_rec l' (cons ltac:(st T) n) (cons y env) body in
       exact r))
     with
     | (fun _: nat => ?r) => constr:(ex n  ltac:(st T) r)
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

Ltac reify_goal_eq l :=
 lazymatch goal with
 | |- ?g => let r := reify_eq_rec l (@nil sort)  (@nil nat) g in change (coerce (@nil sort) r I)
 end.
  

Ltac reify_hyp_eq l h :=
 lazymatch goal with
 | h : ?g |- _ => let r := reify_eq_rec l (@nil sort)  (@nil nat) g in (change (coerce (@nil sort) r I) in h)
 end.*)

(* Once a back or forward steps is performed, we want to apply simplification
   (simpl function).
  For that we need to translate the o3 back into a cx *)


  
Definition empty_inst : inst'.
apply nil.
Defined.


Goal (2=2 /\ 3=3) ->  (2=2 /\ 3=3).
  intro xx.
  
back xx  ((cons false (@nil bool)))
     ((cons false (@nil bool)))
     (cons true (cons false nil)) empty_inst.

back xx  ( (cons false (@nil bool)))  ( ( (@nil bool))) (cons false ( nil)) empty_inst.
Abort.

(* for testing and playing : some inst *)
Definition ex_ex : inst'.
apply cons; last apply nil.
apply None.
Defined.
Definition ex_ex' : inst'.
apply cons; last apply nil.
apply Some.
exists 0.
intros e1 e2; apply e1.
exact 0.
Defined.

Definition ex_ex2 : inst.
unfold inst.
apply (cons None).
apply (cons None).
apply nil.
Defined.


Print cons.

Goal (exists x, x=2 /\ 3=3) -> exists y, y=2 /\ 3=3.
  move => xx.

  

  back xx  [::false; true]  [::false; true]
       [::true; false; false ; true] ex_ex.
 back xx  [::false; false]  [::false]
      [::false; true; false] ex_ex'.
Abort.

  
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
 
