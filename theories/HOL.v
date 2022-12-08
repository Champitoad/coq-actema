From mathcomp Require Import ssreflect ssreflect.seq.


Definition ls := seq {T:Type & T}.

Fixpoint sl (l:ls)(n:nat){struct l} : Type :=
  match l,n with
  | nil, _ => unit
  | cons (existT s _)  _, 0 => s
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

Definition pst ts := {a : (list nat) & (predt ts a)}.
(* Definition eq_arity : pst lsar.
exists (cons 0 (cons 0 nil)).
exact (@eq nat).
Defined.
*)
Definition FOsign :=
  {ts : ls & (list (cst ts) * (list (pst ts)))%type}.

(* ce qui est donné *)
(* Definition sfo : FOsign.
exists lsar.
split.
exact (cons p_op (cons m_op nil)).
exact (cons eq_arity nil).
Defined.
*)
(* Definition ts (sl:FOsign) :=  let (ts, _) := sl in ts. *)
Definition sort ls n :=  sl ls n.

Definition def sl : forall n, sort sl n.
elim: sl => [|[T t] sl def][|n]/=.
exact tt.
exact tt.
exact t.
apply def.
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

Definition trs fs s1 s2 :  sort fs s1 -> sort fs s2.
  case e: (eqnqtdec s1 s2) => [s12|s12].
rewrite s12 => v; exact v.
move => _ ; apply def.
Defined.

Section s_cx.
  Variable ts : ls.
Check def ts.

Lemma trs_corr : forall s v, trs ts s s v = v.
  move => s v; rewrite /trs /protect_term .
by rewrite  eqnqtdec_refl.
Qed.

Definition nthc
           (c:seq nat)(p : ppp ts c)(n:nat): (sort ts (nth 0 c n)).
move: n p.
elim: c => [| t c rc] [|n].  
- move => _ ; apply def.
- move => _ ; apply def.
- move => [x _]; exact x.
- move => [_ x]; exact (rc n x).
Defined.




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
| fa : forall n s, cx (cons s n) -> cx n
| ex : forall n s, cx (cons s n) -> cx n
| equality : forall n s,
    ((ppp ts n) -> (sort ts s)) ->((ppp ts n) -> (sort ts s)) -> cx n
| property  : forall n s,
    ((ppp ts (cons s n)) -> Prop) ->
    ((ppp ts n) -> (sort ts s))  -> cx n.

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

Fixpoint defs l : ppp ts l :=
  match l with
  | nil => tt
  | cons n l => (def ts n, defs l)
  end.


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
| fa3 : forall s, (sort ts s -> o3) -> o3
| ex3 : forall s,  (sort ts s -> o3) -> o3.

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

Definition inst  :=
  list
    (option
       {s & {n1 : ct & {n2 : ct & (pp n1)->(pp n2) -> sort ts s}}}).

(* using an inst *)

Definition env := forall s, nat -> sort ts s.

Definition inst1 := {s : nat & env -> env -> sort ts s}.


Definition trad1 : forall n, pp n -> env :=
  fun n p s i =>
    trs ts (nth 0 n i) s
        (nthc n p i).


Definition trad :
  inst1 -> ct -> ct ->
  {s & {n1 : ct & {n2 : ct & (pp n1)->(pp n2) -> sort ts s}}}.
move => [s f] n1 n2.
exists s; exists n1; exists n2.
move => p1 p2.
exact (f (trad1 n1 p1)(trad1 n2 p2)). 
Defined.

Definition inst' := list (option inst1).



Definition appist1 sr
           (f:{s : nat &
                     {n1 : _ &
                             {n2 : _ & (pp n1)->(pp n2) -> sort ts s}}})
           n1 (i1 : pp n1) n2 (i2 : pp n2) :=
  match f with
    existT  s (existT  m1 (existT  m2 f)) =>
      trs ts  s sr (f (convert n1 m1 i1)(convert n2 m2 i2))
  end.

Definition appist sr (g: inst1) n1 c1 n2 c2 :=
  match g with
    existT s f => trs ts  s sr (f (trad1 n1 c1)(trad1 n2 c2))
  end.


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
                       =(trs ts s s' (v (convert ng ng' gi))))))
                (P (trs ts s' s (t (convert nh nh' hi)),
                     (convert ng ng' gi)))
          | _ => bot3
          end

      | (impl ng' h B) =>
          (impl3 (f3 l ist nh hyp hi ng' h (convert ng ng' gi))
                 (B (convert ng ng' gi)))
      | cNot ng' h =>
          not3
            (f3 l ist nh hyp hi
                ng' h
                (convert ng ng' gi))
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
                     =(trs ts s' s (v (convert ng ng' gi))))))
                    (P ((trs ts s s' (u (convert nh nh' hi))),
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
      | cNot _ _ => bot3
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
              impl3
                (Hol3 (s1 = s2 /\
                ((v (convert n2 n2' i2)  =
                    (trs ts s1 s2 (u (convert n1 n1' i1)))))))
                  (P (convert (cons s2 n2)(cons s2 n2')
                             ((trs ts s1 s2 (t (convert n1 n1' i1))),
                               i2)))
          | _ => top3
          end
      | property n1' s1 P v =>
          match h2 with
         | equality n2' s2 t u =>
              impl3
                (Hol3 (s1 = s2 /\
                ((v (convert n1 n1' i1)  =
                    (trs ts s2 s1 (u (convert n2 n2' i2)))))))
                  (P (convert (cons s1 n1)(cons s1 n1')
                             ((trs ts s2 s1 (t (convert n2 n2' i2))),
                               i1)))
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
      | cNot n1' h1' =>
          not3
            (b3 l ist n2 h2 i2 n1' h1'
                (convert n1 n1' i1))
      | impr n1' B h1' =>
          impr3  (B (convert n1 n1' i1))
                 (f3 l ist n1' h1' (convert n1 n1' i1) n2 h2 i2)
      | fa n1' s1 h1' =>
          match ist with
            | cons None ist =>
                fa3 s1 (fun n =>
                    (f3 l ist (cons s1 n1') h1'
                        (convert (cons s1 n1)(cons s1 n1') (n, i1))
                        n2 h2 i2))
          | cons (Some f) ist =>
              (f3 l ist (cons s1 n1') h1'
                  (convert (cons s1 n1)(cons s1 n1')
                           ((appist s1 f n1 i1 n2 i2),i1))
                  n2 h2 i2)
          | _ => top3
          end
      | ex n1' s1 h1' =>
          ex3 s1
              (fun n =>
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
              impl3
                (Hol3 (s1=s2 /\
                     ((v (convert n2 n2' i2)=
                         (trs ts s1 s2 (t (convert n1 n1' i1)))))))
               (P (convert (cons s2 n2)(cons s2 n2')
                            ((trs ts s1 s2 (u (convert n1 n1' i1))),
                              i2)))
          | _ => top3
          end
    
       | equality n2' s2 t u =>
           match h1 with
           | property n1' s1 P v =>
              impl3
                (Hol3 (s1=s2 /\
                     ((v (convert n1 n1' i1)=
                         (trs ts s2 s1 (t (convert n2 n2' i2)))))))
               (P (convert (cons s1 n1)(cons s1 n1')
                            ((trs ts s2 s1 (u (convert n2 n2' i2))),
                              i1)))

           |_ => top3
           end
      | andl n2' h2' B =>
          f3 l ist n1 h1 i1  n2' h2' (convert n2 n2' i2)
      | andr n2' B h2' =>
          f3 l ist n1 h1 i1 n2' h2' (convert n2 n2' i2)
     | orl  n2' h2' B =>
          orl3 
               (f3 l ist n1 h1 i1 n2' h2' (convert n2 n2' i2))
               (B (convert n2 n2' i2)) 
      | orr n2' B h2' =>
          orr3 (B (convert n2 n2' i2))
               (f3 l ist n1 h1 i1 n2' h2' (convert n2 n2' i2)) 
      | impl n2' h2' B =>
          impl3 (b3 l ist n1 h1 i1 n2' h2' (convert n2 n2' i2))
                (B (convert n2 n2' i2))
       | cNot n2' h2' =>
           not3
             (b3 l ist n1 h1 i1 n2' h2'
                 (convert n2 n2' i2))
      | impr n2' B h2' =>
          impr3  (B (convert n2 n2' i2))
                 (f3 l ist n1 h1 i1 n2' h2' (convert n2 n2' i2) )
       | fa n2' s2 h2' =>
          match ist with
            | cons None ist =>
                fa3 s2 (fun n =>
                 (f3 l ist n1 h1 i1
                     (cons s2 n2') h2'
                     (convert (cons s2 n2)(cons s2 n2') (n, i2))
                 )) 
          | cons (Some f) ist =>
              (f3 l ist n1 h1 i1
                  (cons s2 n2') h2'
                  (convert (cons s2 n2)(cons s2 n2')
                           ((appist s2 f n1 i1 n2 i2),i2))
                  )
          | _ => top3
         end
       | ex n2' s2 h2' =>
           ex3 s2
               (fun n =>
                  (f3 l ist n1 h1 i1
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
   [nh'|nh'|nh' P|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
       |nh' P h|nh' h P|s' nh' h|s' nh' h|nh' t u|nh P v]//= hi
   [|sg ng]
   [ng'|ng'|ng' Q| ng' Q|ng' Q g|ng' g Q|ng' Q g|ng' g Q
       |ng' Q g|ng' g Q|sg' ng' g|sg' ng' g|ng' t' u'|ng' P' v']
   gi //=;
  rewrite /= ?convert_corr ?ppce//=; move => [-> h2] e//=.
- move => ist nh hyp hi ng
          [ng'|ng'|ng' Q|ng' Q|ng' Q g|ng' g Q|ng' Q g|ng' g Q
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
        [nh'|nh'|nh' P|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
        |nh' P h|nh' h P|nh' s h|nh' s h|nh' s t u
        |nh' s P v] //=P2 i2;
      rewrite ?convert_corr; eauto;
   try (by case: i2; eauto);
  move: P2 i2 hr1 => i2 pv;
  induction h1; try done;
    try (by case:  ist => [|[f|] ist] //=; eauto);
    try (by move: IHh1; case:  ist => [|[f|] ist] //=; eauto);
    try (by case: pv => [p hp] c; exists p;
         eapply hl2; auto; rewrite trs_corr; auto).

move => h [e1 e2].
rewrite trs_corr.
move:  t u pv s1  e2 h.  
rewrite -e1.
move => h1 h2 s1 s2.

rewrite !trs_corr convert_corr s1.
simpl. by move <-.
  by rewrite /= convert_corr; move => [e1  [e3 e2]];
      rewrite trs_corr -e1 -e2.

- move => ist nh
          [nh'|nh'|nh' P|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
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
          [nh'|nh'|nh' P|nh' P|nh' P h|nh' h P|nh' P h
              |nh' h P|nh' P h|nh' h P|nh' s h|nh' s h
              |nh' s t u|nh' s P v] /= 
         i1 n2 h2 i2 p1 p2 //=;
  rewrite ?convert_corr; try (by intuition; eauto).
    case: ist =>[//=|[f|] ist]; eauto; move => p; eauto.
    move: p1 => [p1 hp]; exists p1; rewrite trs_corr; eauto.

 induction h2; try done.
 rewrite /=; move => [e1 e2]; move: e2 p2.
 rewrite /=  trs_corr convert_corr.
 move: i1 p1 P s1; rewrite -e1; move => i1 -> P s1.
 rewrite trs_corr.
by move ->.  

  induction h2; try done.
move => [e1 e2].
rewrite trs_corr.
move: s1 s2 e2 p2 p1.  
rewrite -e1.
move => s1 s2; rewrite !trs_corr convert_corr.
by move => -> ->.
Qed.


Definition trl3 := nosimpl tr3.


(* The two actuallly used corollaries *)
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

(* The function instantiating an inner quantifier *)
Fixpoint instp (t:nat)(s : nat)(o : sort ts s)(n : seq nat)
         (c : pp n)(h : cx n) : Prop :=
  match t with
  | 0 =>
      match h with
      | fa n' s' h' =>
          (coerce (s'::n')
                   h'
                   (convert (s::n)(s'::n')(o,c)))
      | _ => True
      end
  | S t =>
      match h with
      | impl n' h' B =>
           (instn t s o n' (convert n n' c) h')->
              (B (convert n n' c))
      | impr n' B h' =>
          (B (convert n n' c)) -> (instp t s o n' (convert n n' c) h')
      | orl n' h' B =>
          ( instp t s o n' (convert n n' c) h') \/(B (convert n n' c))
      | orr n' B h' =>
           (B (convert n n' c)) \/(instp t s o n' (convert n n' c) h')
      |  andl n' h' B =>
          ( instp t s o n' (convert n n' c) h') /\(B (convert n n' c))
      | andr n' B h' =>
          (B (convert n n' c)) /\(instp t s o n' (convert n n' c) h')
      | fa n' s' h' =>
          forall x : sort ts s',
            ( instp t s o (s'::n') (convert (s'::n)(s'::n') (x,c)) h')
     | ex n' s' h' =>
          exists x : sort ts s',
            ( instp t s o (s'::n') (convert (s'::n)(s'::n') (x,c)) h')
      | X => True
      end
  end
with
instn (t:nat)(s : nat)(o : sort ts s)(n : seq nat)
         (c : pp n)(h : cx n) : Prop :=
  match t with
  | 0 =>
      match h with
      | ex n' s' h' =>
          (coerce (s'::n')
                   h'
                   (convert (s::n)(s'::n')(o,c)))
      | _ => False  
      end
  | S t =>
         match h with
      | impl n' h' B =>
           (instp t s o n' (convert n n' c) h')->
              (B (convert n n' c))
      | impr n' B h' =>
          (B (convert n n' c)) -> (instn t s o n' (convert n n' c) h')
      | orl n' h' B =>
          ( instn t s o n' (convert n n' c) h') \/(B (convert n n' c))
      | orr n' B h' =>
           (B (convert n n' c)) \/(instn t s o n' (convert n n' c) h')
      |  andl n' h' B =>
          ( instn t s o n' (convert n n' c) h') /\(B (convert n n' c))
      | andr n' B h' =>
          (B (convert n n' c)) /\(instn t s o n' (convert n n' c) h')
      | fa n' s' h' =>
          forall x : sort ts s',
            ( instn t s o (s'::n') (convert (s'::n)(s'::n') (x,c)) h')
      | ex n' s' h' =>
          exists x : sort ts s',
            ( instn t s o (s'::n') (convert (s'::n)(s'::n') (x,c)) h')
      | X => False
      end
  end.
   

Lemma inst_corr :
  forall t s o n h c,
 ((coerce n h c) ->  (instp t s o n c h))/\
   ((instn t s o n c h) -> (coerce n h c)).
  elim => [/=|t ht] s o n h.
- case h; try done.
     clear h n.  
      move => n s' h c; split; last done.
      intro h'; rewrite convert_corr; apply h'.
     clear h n.  
     move => n s' h c; split; first done.
     rewrite convert_corr.
     by move => h'; exists (trs ts s s' o).
- case: h =>    
          [n'|n'|n' h'|n' Q|n' Q h'|n' h' Q|n' Q h'|n' h' Q|
            n' Q h'|n' h' Q| n' s' h'|n' s' h'|n' s' t1 t2|
            n' s' Q t1] c; split; try (simpl; rewrite ?ppce; done);
   try (by move: (ht _ o _ h' c)=> [ht1 ht2]; rewrite /= convert_corr; auto; try tauto).  
 * move => h''; simpl in h''. move => x; move: (ht _ o _ h' (x,c)) => [ht1 ht2].
   rewrite convert_corr; auto.
 * move => h''; simpl in h''; move => x; move: (h'' x) => h2;
   move: (ht _ o _ h' (x,c)) => [ht1 ht2]; apply ht2.
   by move: h2; rewrite convert_corr trs_corr.
 * move => [x hx].
   exists x.
   rewrite convert_corr.
   by move: (ht _ o _ h' (x,c)) => [ht1 ht2]; auto.
 * move => [x hx].
   exists x.
   move: (ht _ o _ h' (x,c)) => [ht1 ht2]; auto.
   apply ht2.
   by rewrite convert_corr in hx.
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
  | fa3 s p =>  forall n,   (trex (p n))
  | ex3 s p => forall n, (trex (p n))
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
  | fa3 s p =>  forall n,   (trexe (p n))
  | ex3 s p => forall n, (trexe (p n))
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
  | fa3 s f => fa3 s (fun n => o3_norm (f n))
  | ex3 s f => ex3 s (fun n => o3_norm (f n))
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
  | fa3 s f => fa3 s (fun n => o3_norme (f n))
  | ex3 s f => ex3 s (fun n => o3_norme (f n))
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
  | fa3 s f => forall n,  o3_id (f n) Q
  | ex3 s f => forall n,  o3_id (f n) Q
  | top3 => True
  | bot3 => True
  end.

Lemma o3_norm_corr :
  forall Q o, (o3_id o Q) -> (tr3 o)<->(tr3(o3_norm o)).
  move=> Q.
  elim => [P|||o|o ho B|B o ho|o ho B|B o ho|o ho B|B o ho
          |s f hf|s f hf]=>/= h; split; auto; first (by rewrite h);
try          move: (ho h) => [h1 h2];
auto; try (by intuition);
try (by move => hn n; case: (hf n); auto);
move => [n hn]; case: (hf n); eauto.
Qed.



Lemma trex_norm_corr : forall o, (trex o) ->
                                 (tr3 o)<->(tr3(o3_norm o)).
elim => [P|||o|o ho B|B o ho|o ho B|B o ho|o ho B|B o ho
        |s f hf|s f hf]=>/= h; split;
        (try case (ho h) => h1 h2); auto;
        try  tauto;
        try (by move => hn n; case: (hf n); auto);
        move => [n hn]; case: (hf n); eauto.
Qed.


Lemma trex_norme_corr :
  forall o, (trexe o) -> (tr3 o)<->(tr3(o3_norme o)).
Proof.
elim => [P|||o|o ho B|B o ho|o ho B|B o ho|o ho B|B o ho
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



(* Tactics for reification *)



Definition dyn := {T:Type & T}.

Fixpoint tpp (l : seq Type) : Type :=
  match l with
  | cons T l =>  T * (tpp l)
  | _ => unit
  end.
Print tpp.

  Inductive s3 : (seq Type) -> Type :=
  | box : forall n, (tpp n -> Prop) -> s3 n
  | t3 :  forall n, s3 n
  | bo3 : forall n, s3 n
  | n3 :  forall n, s3 n -> s3 n
  | i3 :  forall n, s3 n -> s3 n -> s3 n
  | d3 :  forall n, s3 n -> s3 n -> s3 n
  | c3 :  forall n, s3 n -> s3 n -> s3 n
  | fs3 : forall T n, s3 (cons T n) -> s3 n
  | e3 : forall T n, s3 (cons T n) -> s3 n
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
  | fs3 s n' e, i => forall x: s,
      cs3 (cons s n') e (x,i)
  | e3 s n' e, i => exists x: s,
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
  | fs3 s n' a =>
      if (eT _ (simplc (s::n') a))
      then t3 n'
      else fs3 _ _ (simplc _ a)
  | e3 s n' a =>
           if (eB _ (simplc (s::n') a))
      then bo3 n'
      else e3 _ _ (simplc _ a)
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
       |s n a|s n a] i //= ;split => h;
                                     try (move: (hr _ a i) => [ha1 ha2]);
                                     try (move: (hr _ b i) => [hb1 hb2]);
                                     try (by
induction (simplc n a); move: ha1 ha2 h; simpl; try tauto);
try (by
move: h;
induction (simplc n a);
  induction (simplc n b);
  move: ha1 ha2 hb1 hb2; simpl; try tauto).
case e : eT => //= x;
move:  (hr _ a (x,i))
     => [ha1 ha2]; auto.
move: h; case e : eT => //= h x;
                        move: (hr _ a (x,i))=>[ha1 ha2];
                        auto.
move: (eTc _ _ e) ha1 ha2=> ->; auto.

move: h=>[x hx].
case e : eB;
                        move: (hr _ a (x,i))=>[ha1 ha2];
                        auto.
move: (eBc _ _ e) ha1 ha2=> ->; eauto.
exists x; auto.

move: h; case e : eB => //=.
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

  
Ltac sreify_rec n env t :=
  match t with
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
                      (cons (@existT Type (fun x => x) T y) env)
                      body
           in
              exact r))
     with
     | (fun _: T => ?r) => constr:(fs3 T n r) 
     end
  | exists x: ?T, @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: T => ltac:(
           let body := beta1 body' y in
           let r := sreify_rec
                      (@cons Type T n)
                      (cons (@existT Type (fun x => x) T y) env)
                      body
           in
              exact r))
     with
     | (fun _: T => ?r) => constr:(e3 T n r) 
     end
  | _ =>
          constr:(box n (fun (z: tpp n) =>
                   ltac:(let r := wrap env z t in
                                  exact r))) 

end.



Ltac sreify_goal :=
  match goal with
  | |- ?g =>
      let r := sreify_rec  (@nil Type)  (@nil dyn)  g in
     change (cs3 nil r tt)
  end.

Ltac simplify_goal :=
  sreify_goal;
  apply simplc_corrg;
  rewrite /simplc /eB /eT /cs3.

Ltac sreify_hyp h :=
  match goal with
  | h : ?g |- _ =>
         let r := sreify_rec  (@nil Type)  (@nil dyn)  g in
     change (cs3 (@nil Type) r tt) in h
  end.

Ltac simplify_hyp h :=
  sreify_hyp h;
  move: (simplc_corrh _ _ _ h);
  clear h;
  move => h;
  rewrite /simplc /eB /eT /cs3  in h.

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
       list_args_r f (@cons dyn (existT  (fun X:Type => X) A a) l)
  | ?t => 
      let T := type of t in
      constr:(@cons dyn (@existT Type (fun X:Type => X) T t) l)
  end.

Ltac list_args t :=
  list_args_r t (@nil dyn).

Ltac extract t :=
  match t with
   | (existT _ _  ?f) => f
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
(*
Ltac test t :=
  let r := rebuild ltac:(list_args t) in r.
*)
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

Ltac treplace  d t p :=
  match p with
  | nil => d
  | cons ?n ?p' =>
      let l := list_args t in
      let t' := extract ltac:(tnth l (S n)) in
      let x' := treplace d t' p' in
      let l' :=  ttreplace constr:(@existT Type (fun X => X) _ x') (S n) l in
      let r := rebuild l'
      in r
end.

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


Ltac simpl_path_r p t :=
  match p with
  | nil =>  eval simpl in t
  | cons ?n ?p' =>
      match t with
      | ?a -> ?b =>
          let c := constr:(imp_fun a b) in
          let c' := simpl_path_r p c in
          let r := eval red in c' in r
      |  forall x: ?T, @?body' x => 
          constr:(forall x : T,
                     ltac:(let body := beta1 body' x in
                           let r := simpl_path_r p' body in
                           exact r))
      |  exists x: ?T, @?body' x => 
          constr:(exists x : T,
                     ltac:(let body := beta1 body' x in
                           let r := simpl_path_r p' body in
                           exact r))
      | fun x : ?T => @?body' x => 
          constr:(fun x : T =>
                     ltac:(let body := beta1 body' x in
                           let r := simpl_path_r p' body in
                           exact r))
      | (?f0 _) =>
          let l := list_args t in
          let u := simpl_path_r p' ltac:(extract ltac:(tnth l (S n))) in
          let l' := ttreplace constr:(@existT Type (fun X => X) _ u) (S n) l in
          let r := rebuild l'
          in r
      end
  end.

Ltac simpl_path p :=
  match goal with
  | |- ?g =>
      let g' := simpl_path_r p g in
      change g'
  end.

Ltac simpl_path_hyp h p :=
  let g := type of h in
  let g' := simpl_path_r p g in
  change g' in h.

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
        rebuild constr:(cons (@existT Type (fun X => X) _ t) l)
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
              let r := rebuild constr:(cons (@existT Type (fun X => X) _ g') l') in
                      let r'' := (eval compute in r) in
                      exact r'')
                         | _ => ltac:(
                                        let r := (  beta_head g' l') in exact r)
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
          let u := unfold_path_r p' ltac:(extract ltac:(tnth l (S n))) in
          let l' := ttreplace constr:(@existT Type (fun X => X) _ u) (S n) l in
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
  | cons  (existT _ U _) ?y  => constr:(n)
  | cons  _ ?l1  => st_aux constr:(S n) l1 T
  end.

Ltac tst ts T := (st_aux constr:(0) constr:(ts) T). 

Definition IDT := fun X:Type => X.

Inductive listn :=
  niln | consn : nat -> listn -> listn.
Definition test := (cons  (existT IDT nat 0)
                        (cons (existT IDT bool true)
                              (cons (existT IDT Prop True)
                   (cons (existT IDT listn niln) nil)))).

Ltac preify_rec ts p l n env t :=
  lazymatch constr:(l) with
  | nil =>
      let t' := find_pat t p in 
      let T :=  type of t' in
      let s := tst ts T in
      let y := fresh "y" in
      let x := fresh "zz" in
      let Q := vabst x T t p in 
      let Q' :=
        constr:(fun y : T =>
                fun z : ppp ts (cons s n) =>
                  ltac:(
                          let b := beta1 Q y in
                          let r :=
                            wrap
                              (cons (@existT Type (fun x => x) T y) env)
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
                              ltac:(let r := wrap env z a in exact r)) in
          let rb := preify_rec ts p l' n  env b in
          constr:(impr _ n ra rb)
    | ?a /\ ?b => 
          let ra := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := preify_rec ts p l' n  env b in
          constr:(andr _ n ra rb) 
    | ?a \/ ?b => 
          let ra := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z a in exact r)) in
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
                      ltac:(let r := wrap env z b in exact r)) in
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
                                             (cons (@existT Type (fun x => x) a y) env)
                                             b in
                         exact r))
          in
          match br with
          | (fun _: a => ?r) => constr:(fa ts n
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
                               (cons (@existT Type (fun x => x) T y) env)
                               body in
              exact r))
     with
     | (fun _: _ => ?r) => constr:(fa ts n s r) 
     end 
       | exists x: ?T, @?body' x =>
          let s := tst ts T in
          let y := fresh "y" in
          lazymatch constr:(fun y: T => ltac:(
           let body := beta1 body' y in
           let r := preify_rec ts p l'
                               (cons s n)
                               (cons (@existT Type (fun x => x) T y) env)
                               body in
              exact r))
     with
     | (fun _: _ => ?r) => constr:(ex ts n s r) 
     end 
      | ?a /\ ?b => 
          let rb := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := preify_rec ts p l' n  env a in
          constr:(andl _ n ra rb) 
      | ?a \/ ?b => 
          let rb := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := preify_rec ts p l' n  env a in
          constr:(orl _ n ra rb) 
     
        | _ => constr:(Hole ts n (fun (z: ppp ts n) =>
                               ltac:(let r := wrap env z t in exact r)))
     
      end
end.

Ltac reify_prop ts p l :=
  match goal with
  | |- ?g =>
      let gs := preify_rec ts p l (@nil nat)(@nil dyn) g in
      change (coerce ts (@nil nat) gs tt)
  end.

Ltac reify_prop_hyp ts h h' p l :=
  let gs := preify_rec ts p l  (@nil nat)(@nil dyn) ltac:(type of h) in
  have h' : (coerce ts (@nil nat) gs tt) by assumption.
  

Check ltac:( let r := 
preify_rec test
                         (cons 1 nil)(@nil bool)
                         (@nil nat)(@nil dyn)
                          (4 = 3)
 in exact r).


        
Goal ( 3 = 3) -> True.
  move => a.
  Check ltac:(let gs := preify_rec test (cons 2 nil) (@nil bool)  (@nil nat)(@nil dyn) ltac:(type of a) in exact gs).
Abort.
        
Goal (exists x : nat, 3 = 3) -> True.
  move => a.
reify_prop_hyp test a b (@nil nat)(cons false nil).
Abort.

Goal 3=3 /\4=4 -> True.
  move => a.
reify_prop_hyp test a b (@nil nat)(cons false nil).
Abort.


Ltac reify_eq_rec ts' l n env t :=  
  let ts := eval cbn in ts' in
  lazymatch constr:(l) with
  | nil =>
      match t with
      | ?t1 = ?t2 =>
          let T := type of t1 in
          let s := tst ts T in
          let r1 := constr:(fun (z: ppp ts n) =>
                              ltac:(let r := wrap env z t1 in exact r)) in
          let r2 := constr:(fun (z: ppp ts n) =>
                              ltac:(let r := wrap env z t2 in exact r)) in
          constr:(equality ts n s r1 r2)
      end
  | cons true ?l' =>
      lazymatch t with
      | ?a -> ?b => 
          let ra := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_eq_rec ts l' n  env b in
          constr:(impr _ n ra rb) 
    | ?a /\ ?b => 
          let ra := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_eq_rec ts l' n  env b in
          constr:(andr _ n ra rb) 
    | ?a \/ ?b => 
          let ra := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_eq_rec ts l' n  env b in
          constr:(orr _ n ra rb) 
       end
  | cons false ?l' =>
      lazymatch t with
      | not ?a =>
          let ra := reify_eq_rec ts l' n  env a in
          constr:(cNot _ n ra)
       | forall x: (sort _ ?s), @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: (sort ts s) => ltac:(
           let body := beta1 body' y in
              let r := reify_eq_rec ts l' (cons s n) (cons (@existT Type (fun x => x) (sort ts s) y) env) body in
              exact r))
     with
     | (fun _: (sort ts s) => ?r) => constr:(fa ts n s r) 
     end
      | ?a -> ?b =>
          match type of a with
          | Prop =>       let rb :=
              constr:(fun (z: ppp ts n) =>
                        ltac:(let r := wrap env z b in exact r)) in
            let ra := reify_eq_rec ts l' n  env a in
            constr:(impl _ n ra rb)
          | _ =>
          let s := tst ts a in
                    let y := fresh "y" in
          lazymatch constr:(fun y: (sort ts s) => ltac:(
              let r := reify_eq_rec ts l' (cons s n) (cons (@existT Type (fun x => x) (sort ts s) y) env) b in
              exact r))
     with
     | (fun _: (sort ts s) => ?r) => constr:(fa ts n s r) 
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
              let r := reify_eq_rec ts l' (cons s n) (cons (@existT Type (fun x => x) T y) env) body in
              exact r))
     with
     | (fun _: T => ?r) => constr:(fa ts n ltac:(let s := tst ts T in exact s) r) 
     end
      | exists x: ?T, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: T => ltac:(
          let body := beta1 body' y in
          let s := ltac:(tst ts T) in
       let r := reify_eq_rec ts l' (cons
                               s
                               n) (cons  (@existT Type (fun x => x) T y) env) body in
       exact r))
     with
     | (fun _: T => ?r) => constr:(ex ts n
                                      ltac:(let s := tst ts T in exact s) r)
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
      let gs := reify_eq_rec ts l (@nil nat)(@nil dyn) g in
      change (coerce ts (@nil nat) gs tt)
  end.

Ltac reify_eq_hyp ts h h' l :=
  let g := type of h in
  let gs := reify_eq_rec ts l (@nil nat)(@nil dyn) g in
  have h' : (coerce  ts (@nil nat) gs tt) by assumption.

  
Ltac reify_rec ts' l n env t :=
  let ts := eval compute in ts' in
  lazymatch constr:(l) with
    | nil => constr:(Hole ts n (fun (z: ppp ts n) =>
                               ltac:(let r := wrap env z t in exact r)))
  | cons true ?l' =>
      lazymatch t with
      | ?a -> ?b => 
          let ra := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_rec ts l' n  env b in
          constr:(impr _ n ra rb) 
    | ?a /\ ?b => 
          let ra := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_rec ts l' n  env b in
          constr:(andr _ n ra rb) 
    | ?a \/ ?b => 
          let ra := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_rec ts l' n  env b in
          constr:(orr _ n ra rb) 
       end
  | cons false ?l' =>
      lazymatch t with
      | not ?a =>
          let ra := reify_rec ts l' n  env a in
          constr:(cNot _ n ra)
       | forall x: (sort _ ?s), @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: (sort ts s) => ltac:(
           let body := beta1 body' y in
              let r := reify_rec ts l' (cons s n) (cons (@existT Type (fun x => x) (sort ts s) y) env) body in
              exact r))
     with
     | (fun _: (sort ts s) => ?r) => constr:(fa ts n s r) 
     end

      | ?a -> ?b =>
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
              let r := reify_rec ts l' (cons s n) (cons (@existT Type (fun x => x) a y) env) b in
              exact r))
     with
     | (fun _: a => ?r) => constr:(fa ts n ltac:(let s := tst ts a in exact s) r) 
     end
     end
      | forall x: ?T, @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: T => ltac:(
           let body := beta1 body' y in
           let s := ltac:( tst ts T) in                                  
              let r := reify_rec ts l' (cons s n) (cons (@existT Type (fun x => x) T y) env) body in
              exact r))
     with
     | (fun _: T => ?r) => constr:(fa ts n ltac:(let s := tst ts T in exact s) r) 
     end
      | exists x: ?T, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: T => ltac:(
          let body := beta1 body' y in
          let s := ltac:(tst ts T) in
       let r := reify_rec ts l' (cons
                               s
                               n) (cons  (@existT Type (fun x => x) T y) env) body in
       exact r))
     with
     | (fun _: T => ?r) => constr:(ex ts n
                                      ltac:(let s := tst ts T in exact s) r)
     end   
      | ?a /\ ?b => 
          let rb := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_rec ts l' n  env a in
          constr:(andl _ n ra rb) 
      | ?a \/ ?b => 
          let rb := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_rec ts l' n  env a in
          constr:(orl _ n ra rb) 
     
        | _ => constr:(Hole ts n (fun (z: ppp ts n) =>
                               ltac:(let r := wrap env z t in exact r)))
     
end
  end.

(* same but detecting True and False *)

Ltac reify_rec_at ts' l n env t :=
  let ts := eval cbn in ts' in
  lazymatch constr:(l) with
  | nil =>
      match t with
      | True => constr:(cTop ts n)
      | False => constr:(cBot ts n)
      | _ =>
          constr:(Hole ts n (fun (z: ppp ts n) =>
                            ltac:(let r := wrap env z t in exact r)))
      end
  | cons true ?l' =>
      lazymatch t with
      | ?a -> ?b => 
          let ra := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_rec_at ts l' n  env b in
          constr:(impr _ n ra rb) 
    | ?a /\ ?b => 
          let ra := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_rec_at ts l' n  env b in
          constr:(andr _ n ra rb) 
    | ?a \/ ?b => 
          let ra := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z a in exact r)) in
          let rb := reify_rec_at ts l' n  env b in
          constr:(orr _ n ra rb) 
       end
  | cons false ?l' =>
      lazymatch t with
      | ~ ?a =>
           let ra := reify_rec_at ts l' n  env a in
          constr:(cNot _ n ra)

       | forall x: (sort _ ?s), @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: (sort s) => ltac:(
           let body := beta1 body' y in
              let r := reify_rec_at ts l' (cons s n) (cons (@existT Type (fun x => x) (sort ts s) y) env) body in
              exact r))
     with
     | (fun _: (sort ts s) => ?r) => constr:(fa ts n s r) 
     end
        
      | ?a -> ?b => 
      match type of a with
      | Prop =>
          let rb := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_rec_at ts l' n  env a in
          constr:(impl _ n ra rb) 
       | _ => 
       let y := fresh "y" in
       lazymatch constr:(fun y: a => ltac:(
        let s := ltac:(tst ts a) in                                  
           let r := reify_rec_at ts l' (cons s n) (cons (@existT Type (fun x => x) a y) env) b in
           exact r))
  with
  | (fun _: a => ?r) => constr:(fa ts n ltac:(let s := tst ts a in exact s) r) 
  end end
      | forall x: ?T, @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: T => ltac:(
           let body := beta1 body' y in
           let s := ltac:(tst ts T) in                                  
              let r := reify_rec_at ts l' (cons s n) (cons (@existT Type (fun x => x) T y) env) body in
              exact r))
     with
     | (fun _: T => ?r) => constr:(fa ts n ltac:(let s := tst ts T in exact s) r) 
     end
      | exists x: ?T, @?body' x =>
     let y := fresh "y" in
     lazymatch constr:(fun y: T => ltac:(
          let body := beta1 body' y in
           let s := ltac:(tst ts T) in                         let r := reify_rec_at ts l' (cons
                               s
                               n) (cons  (@existT Type (fun x => x) T y) env) body in
       exact r))
     with
     | (fun _: T => ?r) => constr:(ex ts n
                                      ltac:(let s := tst ts T in exact s)
                                             r)
     end   
      | ?a /\ ?b => 
          let rb := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_rec_at ts l' n  env a in
          constr:(andl _ n ra rb) 
      | ?a \/ ?b => 
          let rb := constr:(fun (z: ppp ts n) =>
                      ltac:(let r := wrap env z b in exact r)) in
          let ra := reify_rec_at l' n  env a in
          constr:(orl _ n ra rb) 
     
        | _ => constr:(Hole ts n (fun (z: ppp ts n) =>
                               ltac:(let r := wrap env z t in exact r)))
     
end
  end.



Ltac reify_goal ts l :=
 lazymatch goal with
 | |- ?g =>
     let r := reify_rec ts l  (@nil nat)  (@nil dyn)  g in
     change (coerce ts (@nil nat) r tt)
 end.

Ltac reify_goal_at ts l :=
 lazymatch goal with
 | |- ?g =>
     let r := reify_rec_at ts l (@nil nat)  (@nil dyn) g in change (coerce ts (@nil nat) r tt)
 end.

Ltac reify_hyp ts l h :=
 let o := type of h in
 match o with
 | ?g =>
     let r := reify_rec ts l (@nil nat)  (@nil dyn) g in (change (coerce ts (@nil nat) r tt) in h)
 end.

Ltac reify_hyp_at ts l h :=
 let o := type of h in
 match o with
 | ?g =>
     let r := reify_rec_at ts l (@nil nat)  (@nil dyn) g in (change (coerce ts (@nil nat) r tt) in h)
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
       rewrite /= ?trs_corr in h';
       rewrite /trs /eqnqtdec /eq_rect_r /eq_rect /nat_rec /eq_sym  /nat_rect /sort in h';
       clear x
   end.

  
Ltac inst_hyp_nd ts l h s o :=
  reify_hyp ts l h;
  let sy := type of h in
   match sy with
   | coerce (@nil nat) ?hc _ =>
       move: (instp_corr ts (pred (length l))  s o (@nil nat) hc tt h);
       clear h; move => h;
       rewrite /= ?trs_corr in h;
        rewrite /trs /eqnqtdec /eq_rect_r /eq_rect /nat_rec /eq_sym  /nat_rect /sort /sl  in h
   end.


  (* Goal (forall X :  Prop,  X) -> False.
intro h.
Eval compute in (sort ts 2).


inst_hyp_nd (cons false nil) h 2 ( False).
by apply h.
Abort. *)




Ltac inst_goal ts l s o :=
  reify_goal ts l;
   match goal with
   | |- coerce _ (@nil nat) ?hc _ =>
      apply (instn_corr ts (pred (length l))  s o (@nil nat) hc tt);
       rewrite /= ?trs_corr
   end.


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

Ltac back ts' h0 hp gp t i :=
  let ts := eval hnf in ts' in
  let h := fresh "h" in
  move: (h0) => h;
  reify_goal ts gp;
  reify_hyp ts hp h;
  let o := type of h in
  match o with
    | coerce _ (@nil nat) ?hc _ =>
        apply (b3_corr ts t i (@nil nat) tt (@nil nat) tt hc);
        [idtac|assumption];
        (apply trex_norm_apply; [simpl; try done; auto|
          rewrite /b3 /o3_norm /coerce ;
          try exact tt];
          rewrite  /trl3 /tr3 /convert /cT /cB /trad /trad1 /nthc /list_rect /sort;
         rewrite /appist /trs /sl  ?eqnqtdec_refl /eq_rect_r
                 /eq_rect /Logic.eq_sym /eq_sym /trad1;
          simplify_goal
        );
        try by apply I
  end;
   rewrite /sort /trad1 /seq.nth /nthc /list_rect /trs /eqnqtdec /nat_rec /nat_rect /eq_rect_r /eq_rect /eq_sym ;
  clear h. 

(*
Parameter A : Prop.
Print test.
Goal A -> forall x:nat,A/\A.
  intro a.
  back [:: existT IDT nat 0; existT IDT bool true; existT IDT Prop True;
    existT IDT listn niln]
       a (@nil bool)(cons false (cons false nil))(cons true (cons true nil))(@nil (option (inst1 test))).  
rewrite /test. *)
  
(* rewrite with hypothesis h in goal 
 hp : list bool = path to the equality
 gp : list bool = path to the atomic proposition containing the term
 gp' : list nat = path to the term
 t : list bool = trace (with the last bool for choice l <-> r)
 i : instantiation *)

Ltac rew_dnd ts' h hp gp gp' t i :=
  let ts := eval compute in ts' in
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
  apply (b3_corr ts t i  (@nil nat) tt (@nil nat) tt
                 ec gc);
  [idtac| try assumption];
  (apply trex_norm_apply ; [try split; try reflexivity|idtac]);
  clear h';
 rewrite /coerce /b3 /trl3 /tr3 /o3_norm ?trs_corr /convert  /defs /appist ?trs_corr;
     rewrite  /coerce /b3 /trl3 /tr3 /o3_norm ?trs_corr /convert /cT /cB  /appist /sort /trad1 /nthc /list_rect /sort /sl;
  rewrite ?trs_corr /trs ?eqnqtdec_refl /eq_rect_r /eq_rect /Logic.eq_sym; 
  simplify_goal;
  rewrite  /sort /sl. 

  
  
(*
Definition iin  : nat -> list (option inst1).
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
         (cons true (cons true nil)) (@nil (option inst1)).
Abort.



Goal P 0 -> 2=0 -> P 2.
intro h.
rew_dnd' h (@nil bool)(cons 0 nil)
         (cons false nil)
         (cons true (cons false nil)) (@nil (option inst1)).
Abort.
*)



(* rewrite with hypothesis h1 in hyp h2 to yield new hyp h3 
 hp1 : list bool = path to the equality
 hp2 : list bool = path to the atomic proposition containing the term
 hp2' : list nat = path to the term
 t : list bool = trace (with the last bool for choice l <-> r)
 i : instantiation *)

Ltac rew_dnd_hyp ts'  h1 h2 h3 hp1 hp2 hp2' t i :=
  let ts := eval compute in ts' in
  let i' := eval compute in i in
  let h1' := fresh "h1" in
  let h2' := fresh "h2" in
  let h4 := fresh "h4" in
  let h5 := fresh "h5" in
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
  move:
    (f3_corr ts  t i' (@nil nat) hc1 tt
             (@nil nat) hc2 tt h1 h2) => h4;
  clear h1' h2';
  let oh4 :=
    match type of h4 with
    | (trl3 _ ?oh) => oh
    end in
  cut (trex ts oh4); [idtac| by split];
  move => h5;
  move: (trex_norm_fapply ts oh4 h5 h4) => h3;
  clear h5 h4;
   rewrite /coerce /sort /trl3 /tr3 /f3 /o3_norm /cT /cB in h3;
   rewrite /convert /trs  ?eqnqtdec_refl /eq_rect_r /eq_rect /Logic.eq_sym in h3;
    rewrite /appist /trs /eqnqtdec /eq_rect_r /eq_rect /nat_rec/nat_rect /protect_term /eq_sym /f_equal /sort /sl in h3;
  simplify_hyp h3. 

      
  
Ltac forward ts h1' h2' h3 hp1 hp2 t i :=
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
           move:
           (f3_corr ts  t i (@nil nat) hc1 tt
                    (@nil nat) hc2 tt h1 h2) => h3
    end
  end;
  apply trex_norm_fapply in h3;
  rewrite /coerce  /= in h1;
  rewrite /coerce /= in h2;
  [ | simpl; try done; auto];
  try clear h1 h2;
  rewrite /coerce /trl3 /f3 /o3_norm /= /cT /cB in h3;
  rewrite /trs /sl /ts  ?eqnqtdec_refl /eq_rect_r /eq_rect /Logic.eq_sym /trad1/trs/eq_rect_r/= in h3;
  simplify_hyp h3;
      match goal with
      | h3 : False |- _ => case h3
      | _ => idtac
      end.

(*
Goal 2=3 -> 3=4.
  intro h.
  Check b3_corr.
  Check andr.

  Check
    ltac:(let r :=
            reify_eq_rec test
                         (@nil bool)(@nil nat)(@nil dyn)(3=4)
                         in exact r).
 

rew_dnd test  h (@nil bool)(cons 1 nil)(@nil bool)(cons true nil)(@nil (option (inst1 test))).
Abort.


Definition iin  : nat -> list (option (inst1 test)).
  intro n.
apply cons; last apply nil.
apply Some; exists 0.
move => *; exact n.
Defined.


Definition idd : list (option (inst1 test)).
apply cons; try apply nil.
apply Some.
exists 0.
intros e1 e2.
apply e2.
exact 0.
Defined.
           


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


Definition ip0 : option (inst1 test).
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
unfold inst1.
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


Ltac myinduction p :=
  match goal with
  | |- ?g =>
      let g' := myinduction_r p g in
      induction g'
  end.


Ltac myinduction_hyp h p :=
  let g := type of h in
  let g' := myinduction_r p g in
  induction g'.
 
