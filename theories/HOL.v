From mathcomp Require Import ssreflect ssreflect.seq.


Inductive DYN :=
  mDYN : forall A:Type, A -> DYN.
Definition ls := seq DYN.

Inductive TDYN :=
  tDYN : Type -> TDYN.
Definition tls := seq TDYN.


Fixpoint sl (l:ls)(n:nat){struct l} : Type :=
  match l,n with
  | nil, _ => unit
  | cons (mDYN s _)  _, 0 => s
  | cons _ l, S n => sl l n
  end.

Fixpoint tsl (l:tls)(n:nat){struct l} : Type :=
  match l,n with
  | nil, _ => unit
  | cons (tDYN s )  _, 0 => s
  | cons _ l, S n => tsl l n
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
Definition wsort (ls:ls) n :=  sl ls n.
Definition sort tls n :=  tsl tls n.


Definition def sl : forall n, wsort sl n.
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

Definition trs fs s1 s2 :  wsort fs s1 -> wsort fs s2.
  case e: (eqnqtdec s1 s2) => [s12|s12].
rewrite s12 => v; exact v.
move => _ ; apply def.
Defined.

Section s_cx.

Variable ts : ls.


Lemma trs_corr : forall s v, trs ts s s v = v.
  move => s v; rewrite /trs /protect_term .
by rewrite  eqnqtdec_refl.
Qed.

Definition nthc
           (c:seq nat)(p : ppp ts c)(n:nat): (wsort ts (nth 0 c n)).
move: n p.
elim: c => [| t c rc] [|n].  
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
| seto : forall n s,
    ((ppp ts n) -> (wsort ts s) -> (wsort ts s) -> Prop) ->
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
| seto _ _ R t u => fun x => R x (t x) (u x)
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
        |n A B hB|n A hA B|n s nv A hA |n s nv A hA|n t u|n R t u|n P t] i //=;
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

Definition inst  :=
  list
    (option
       {s & {n1 : ct & {n2 : ct & (pp n1)->(pp n2) -> wsort ts s}}}).

(* using an inst *)

Definition wenv := forall s, nat -> wsort ts s.

Definition inst2 := {s : nat & wenv -> wenv -> wsort ts s}.


Definition trad1 : forall n, pp n -> wenv :=
  fun n p s i =>  nths s n p i.
(*    trs ts (nth 0 n i) s
        (nthc n p i). *)


Definition trad :
  inst2 -> ct -> ct ->
  {s & {n1 : ct & {n2 : ct & (pp n1)->(pp n2) -> wsort ts s}}}.
move => [s f] n1 n2.
exists s; exists n1; exists n2.
move => p1 p2.
exact (f (trad1 n1 p1)(trad1 n2 p2)). 
Defined.

Definition inst' := list (option inst2).


Definition appist1 sr
           (f:{s : nat &
                     {n1 : _ &
                             {n2 : _ & (pp n1)->(pp n2) -> wsort ts s}}})
           n1 (i1 : pp n1) n2 (i2 : pp n2) :=
  match f with
    existT  s (existT  m1 (existT  m2 f)) =>
      trs ts  s sr (f (convert n1 m1 i1)(convert n2 m2 i2))
  end.

Definition appist sr (g: inst2) n1 c1 n2 c2 :=
  match g with
    existT s f => trs ts  s sr (f (trad1 n1 c1)(trad1 n2 c2))
  end.

  
(* the main functions as described in our CPP 2022 article *)
(* "side conditions" are generated (which are actually in the center
   and not on the side) : 
    - A->B  for the focused formulas (meant to be A->A in practice)
    - two equalites for equality rewrites which should be two trivial
      reflexive equalities
 *)

Definition switch_inst2 (i:inst2) : inst2 :=
  match i with
    existT s f =>
      existT _ s (fun x y => f y x)
  end.

Fixpoint switch_inst (i:inst') : inst' :=
  match i with
  | cons None j => cons None (switch_inst j)
  | cons (Some h) j => cons (Some (switch_inst2 h))
                            (switch_inst j)
  | x => x
  end.

Definition xor b b' :=
  match b, b' with
  | true, true => false
  | false, false => false
  | _, _ => true
  end.

Fixpoint b3 (rw:bool)(l:trace) (b:bool)(ist:inst')(nh:ct)(hyp : cx nh)(hi : pp nh)
         (ng : ct)(goal : cx ng)(gi : pp ng) : o3 :=
  match l  with
  | nil =>
      match hyp, goal with
      | (Hole nh' h), (Hole ng' g) =>
          (Hol3  (h (convert nh nh' hi) ->
                  (g (convert ng ng' gi))))
      | (equality nh' s' t u), (property ng' s P v) =>
          if rw
          then
            andl3  
              (Hol3 (s = s'/\((u (convert nh nh' hi))
                              =(trs ts s s' (v (convert ng ng' gi))))))
              (P (trs ts s' s (t (convert nh nh' hi)),
                     (convert ng ng' gi)))
          else
            andl3  
              (Hol3 (s = s'/\((t (convert nh nh' hi))
                              =(trs ts s s' (v (convert ng ng' gi))))))
              (P (trs ts s' s (u (convert nh nh' hi)),
                   (convert ng ng' gi)))
      | (seto nh' s' R t u), (property ng' s P v) =>
          if rw
          then
            andl3  
              (Hol3 (s = s'/\((u (convert nh nh' hi))
                              =(trs ts s s' (v (convert ng ng' gi))))
                     /\(forall x y,
                           R (convert nh nh' hi) (trs _ _ _ y)
                             (trs _ _ _ x) ->
                           P (y, (convert ng ng' gi)) ->
                           P (x, (convert ng ng' gi)))))
              (P (trs ts s' s (t (convert nh nh' hi)),
                     (convert ng ng' gi)))
          else
 (andl3  
              (Hol3 (s = s'/\((t (convert nh nh' hi))
                              =(trs ts s s' (v (convert ng ng' gi))))
                     /\(forall x y,
                           R (convert nh nh' hi) (trs _ _ _ x)
                             (trs _ _ _ y) ->
                           P (y, (convert ng ng' gi)) ->
                           P (x, (convert ng ng' gi)))))
              (P (trs ts s' s (u (convert nh nh' hi)),
                     (convert ng ng' gi))))
            
       
              
      | _,_ => bot3
          end
  | (cons x l) =>
      match x with
      | true => 
      match goal with
      | (impl ng' h B) =>
          (impl3 (f3 rw l b ist nh hyp hi ng' h (convert ng ng' gi))
                 (B (convert ng ng' gi)))
      | cNot ng' h =>
          not3
            (f3 rw l b ist nh hyp hi
                ng' h
                (convert ng ng' gi))
      | (impr ng'  B g) =>
          (impr3 (B (convert ng ng' gi))
                 (b3 rw l b ist nh hyp hi ng' g (convert ng ng' gi)))
      | orl ng' g B =>
          orl3 (b3 rw l b ist nh hyp hi ng' g (convert ng ng' gi))
               (B (convert ng ng' gi))
      | orr ng' B g =>
          orr3  (B (convert ng ng' gi))
                (b3 rw l b ist nh hyp hi ng' g (convert ng ng' gi))
      | andl ng' g B =>
          andl3 (b3 rw l b ist nh hyp hi ng' g (convert ng ng' gi))
               (B (convert ng ng' gi))
      | andr ng' B g =>
          andr3  (B (convert ng ng' gi))
                 (b3 rw l b ist nh hyp hi ng' g (convert ng ng' gi)) 
      |  (fa ng' s nv g) =>
               fa3 s nv (fun n=>
                  (b3 rw l b ist nh hyp hi (cons s ng') g
                      (n, convert ng ng' gi))) 
      | ex ng' s nv g =>
          match ist with
          | cons (Some f) ist =>
              let f' :=
                if b then (switch_inst2 f)
                else f
              in
              b3 rw l b ist
                 nh hyp hi
                 (cons s ng') g
                 (appist s f' nh hi ng gi,
                   (convert ng ng' gi))
          |  cons None ist =>
               ex3 s nv
                 (fun p =>
                    b3 rw l b ist nh hyp hi
                       (cons s ng') g
                       (p, convert ng ng' gi))
          | nil => bot3
          end  
                
      | cTop _ => top3
                     
      | cBot _ => bot3  
      | Hole _ _ => bot3
      | _ => bot3
      end
  | false =>
      match hyp with
      | andl nh' h B =>
           (b3 rw l b ist nh' h (convert nh nh' hi)
                    ng goal gi)
      | andr nh' B h =>
                 (b3 rw l b ist nh' h (convert nh nh' hi)
                     ng goal gi)
      | orl nh' h B =>
          andl3 (b3 rw l b ist nh' h (convert nh nh' hi)
                   ng goal gi)
               ((B (convert nh nh' hi))->
                (coerce ng goal gi))
      | orr nh' B h =>
          andr3 ((B (convert nh nh' hi))->
                (coerce ng goal gi))
               (b3 rw l b ist nh' h (convert nh nh' hi)
                   ng goal gi) 
      | impr nh' B h =>
          andr3 (B (convert nh nh' hi))
                (b3 rw l b ist nh' h (convert nh nh' hi)
                   ng goal gi)
      | fa n s nv h =>
          match ist with
          | cons (Some f) ist =>
                            let f' :=
                if b then (switch_inst2 f)
                else f
              in

              (b3 rw l b ist
                  (cons s n) h (convert
                         (cons s nh) (cons s n)
                         ((appist s f' nh hi ng gi),hi))
                  ng goal gi)
          | cons None ist =>
              ex3 s nv
                  (fun p =>
                     (b3 rw l b ist
                         (cons s n) h
                         (convert (cons s nh)(cons s n)
                                  (p, hi))
                         ng goal gi))
          | _ => bot3
          end
      | ex n s nv h =>
          fa3 s nv
            (fun p =>
               (b3 rw l b ist
                   (cons s n) h
                   (convert (cons s nh)(cons s n)
                            (p, hi))
                   ng goal gi))
      | impl  nh' h B  => bot3            
      | cNot _ _ => bot3
      | cTop _ => bot3
      | cBot _ => top3
      | Hole _ _ => bot3
      | _ => bot3
      end
      end
  end
with f3 (rw:bool)(l:trace)(b:bool)(ist: inst')(n1:ct)(h1 : cx n1)(i1 : pp n1)
        (n2 : ct)(h2 : cx n2)(i2 : pp n2) :
      o3 :=
  match l with
  | nil =>
      match h1, h2 with
      | equality n1' s1 t u, property n2' s2 P v =>
          if rw then
            impl3
                (Hol3 (s1 = s2 /\
                ((v (convert n2 n2' i2)  =
                    (trs ts s1 s2 (u (convert n1 n1' i1)))))))
                  (P ((trs ts s1 s2 (t (convert n1 n1' i1))),
                         (convert n2 n2' i2)))
          else
           impl3
                (Hol3 (s1 = s2 /\
                ((v (convert n2 n2' i2)  =
                    (trs ts s1 s2 (t (convert n1 n1' i1)))))))
                  (P ((trs ts s1 s2 (u (convert n1 n1' i1))),
                       (convert n2 n2' i2)))

      | property n1' s1 P v, equality n2' s2 t u =>
          if rw then
            impl3
                (Hol3 (s1 = s2 /\
                ((v (convert n1 n1' i1)  =
                    (trs ts s2 s1 (u (convert n2 n2' i2)))))))
                (P (trs ts s2 s1 (t (convert n2 n2' i2)),
                     (convert n1 n1' i1)))
          else
             impl3
                (Hol3 (s1 = s2 /\
                ((v (convert n1 n1' i1)  =
                    (trs ts s2 s1 (t (convert n2 n2' i2)))))))
                (P (trs ts s2 s1 (u (convert n2 n2' i2)),
                     (convert n1 n1' i1)))
     | seto n1' s1 R t u, property n2' s2 P v =>
          if rw then
            impl3
                (Hol3 (s1 = s2 /\
                ( (v (convert n2 n2' i2))  =
                    (trs ts s1 s2 (u (convert n1 n1' i1))))
                       /\(forall x y,
                           R (convert n1 n1' i1) (trs _ _ _ x)
                             (trs _ _ _ y) ->
                           P (y, (convert n2 n2' i2)) ->
                           P (x, (convert n2 n2' i2)))))
                  (P ((trs ts s1 s2 (t (convert n1 n1' i1))),
                         (convert n2 n2' i2)))
          else
           impl3
                (Hol3 (s1 = s2 /\
                ((v (convert n2 n2' i2)  =
                    (trs ts s1 s2 (t (convert n1 n1' i1)))))
                       /\
                         (forall x y,
                           R (convert n1 n1' i1) (trs _ _ _ x)
                             (trs _ _ _ y) ->
                           P (x, (convert n2 n2' i2)) ->
                           P (y, (convert n2 n2' i2)))))
                  (P ((trs ts s1 s2 (u (convert n1 n1' i1))),
                       (convert n2 n2' i2)))

      | property n1' s1 P v, seto n2' s2 R t u =>
          if rw then
            impl3
                (Hol3 (s1 = s2 /\
                ((v (convert n1 n1' i1)  =
                    (trs ts s2 s1 (u (convert n2 n2' i2)))))
                       /\(forall x y,
                           R (convert n2 n2' i2) (trs _ _ _ x)
                             (trs _ _ _ y) ->
                           P (y, (convert n1 n1' i1)) ->
                           P (x, (convert n1 n1' i1)))))
                (P (trs ts s2 s1 (t (convert n2 n2' i2)),
                     (convert n1 n1' i1)))
          else
             impl3
                (Hol3 (s1 = s2 /\
                ((v (convert n1 n1' i1)  =
                    (trs ts s2 s1 (t (convert n2 n2' i2)))))
                  /\(forall x y,
                           R (convert n2 n2' i2) (trs _ _ _ x)
                             (trs _ _ _ y) ->
                           P (x, (convert n1 n1' i1)) ->
                           P (y, (convert n1 n1' i1)))))
                (P (trs ts s2 s1 (u (convert n2 n2' i2)),
                     (convert n1 n1' i1)))
      | _,_ => top3
      end

  | cons x l =>
     match (xor x b) with
     | false => 
      match h1 with
      | andl n1' h1' B =>
          andl3
            (f3 rw l b ist n1' h1' (convert n1 n1' i1) n2 h2 i2)
                            (B (convert n1 n1' i1))
(*          f3 rw l b ist n1' h1' (convert n1 n1' i1) n2 h2 i2 *)
      | andr n1' B h1' =>
          andr3
            (B (convert n1 n1' i1))
            (f3 rw l b ist n1' h1' (convert n1 n1' i1) n2 h2 i2)
(*          f3 rw l b ist n1' h1' (convert n1 n1' i1) n2 h2 i2 *)
      | orl  n1' h1' B =>
          orl3  (f3 rw l b ist n1' h1' (convert n1 n1' i1) n2 h2 i2)
                (B (convert n1 n1' i1))
      | orr n1' B h1' =>
          orr3 (B (convert n1 n1' i1))
               (f3 rw l b ist n1' h1' (convert n1 n1' i1) n2 h2 i2) 
      | impl n1' h1' B =>
          impl3 (b3 rw l (negb b) ist n2 h2 i2 n1' h1'
                    (convert n1 n1' i1))
                (B (convert n1 n1' i1))
      | cNot n1' h1' =>
          not3
            (b3 rw l (negb b) ist n2 h2 i2 n1' h1'
                (convert n1 n1' i1))
      | impr n1' B h1' =>
          impr3  (B (convert n1 n1' i1))
                 (f3 rw l b ist n1' h1' (convert n1 n1' i1) n2 h2 i2)
      | fa n1' s1 nv h1' =>
          match ist with
            | cons None ist =>
                fa3 s1 nv (fun n =>
                    (f3 rw l b ist (cons s1 n1') h1'
                        (convert (cons s1 n1)(cons s1 n1') (n, i1))
                        n2 h2 i2))
          | cons (Some f) ist =>
                            let f' :=
                if b then (switch_inst2 f)
                else f
              in

              (f3 rw l b ist (cons s1 n1') h1'
                  (convert (cons s1 n1)(cons s1 n1')
                           ((appist s1 f' n1 i1 n2 i2),i1))
                  n2 h2 i2)
          | _ => top3
          end
      | ex n1' s1 nv h1' =>
          ex3 s1 nv
              (fun n =>
                 (f3 rw l b ist (cons s1 n1') h1'
                     (convert (cons s1 n1)(cons s1 n1') (n, i1))
                        n2 h2 i2))
      | _ => top3
      end
   |  true  =>
       match h2 with
       | andl n2' h2' B =>
           andl3 
             (f3 rw l b ist n1 h1 i1  n2' h2' (convert n2 n2' i2))
             (B (convert n2 n2' i2)) 
       | andr n2' B h2' =>
           andr3
             (B (convert n2 n2' i2)) 
             (f3 rw l b ist n1 h1 i1 n2' h2' (convert n2 n2' i2))
       | orl  n2' h2' B =>
           orl3 
             (f3 rw l b ist n1 h1 i1 n2' h2' (convert n2 n2' i2))
               (B (convert n2 n2' i2)) 
       | orr n2' B h2' =>
           orr3 (B (convert n2 n2' i2))
                (f3 rw l b ist n1 h1 i1 n2' h2' (convert n2 n2' i2)) 
       | impl n2' h2' B =>
           impl3 (b3 rw l b (switch_inst ist) n1 h1 i1 n2' h2' (convert n2 n2' i2))
                 (B (convert n2 n2' i2))
       | cNot n2' h2' =>
           not3
             (b3 rw l b ist n1 h1 i1 n2' h2'
                 (convert n2 n2' i2))
      | impr n2' B h2' =>
          impr3  (B (convert n2 n2' i2))
                 (f3 rw l b ist n1 h1 i1 n2' h2' (convert n2 n2' i2) )
       | fa n2' s2 nv h2' =>
          match ist with
            | cons None ist =>
                fa3 s2 nv (fun n =>
                 (f3 rw l b ist n1 h1 i1
                     (cons s2 n2') h2'
                     (convert (cons s2 n2)(cons s2 n2') (n, i2))
                 )) 
          | cons (Some f) ist =>
                            let f' :=
                if b then (switch_inst2 f)
                else f
              in

              (f3 rw l b ist n1 h1 i1
                  (cons s2 n2') h2'
                  (convert (cons s2 n2)(cons s2 n2')
                           ((appist s2 f' n1 i1 n2 i2),i2))
                  )
          | _ => top3
         end
       | ex n2' s2 nv h2' =>
           ex3 s2 nv
               (fun n =>
                  (f3 rw l b ist n1 h1 i1
                      (cons s2 n2') h2'
                   (convert (cons s2 n2)(cons s2 n2') (n, i2))
                 )) 
      | _ => top3
      end
     end
  end.
(*
Fixpoint b3' (l:trace)(ist:inst)(nh:ct)(hyp : cx nh)(hi : pp nh)
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
          (impl3 (f3' l ist nh hyp hi ng' h (convert ng ng' gi))
                 (B (convert ng ng' gi)))
      | cNot ng' h =>
          not3
            (f3' l ist nh hyp hi
                ng' h
                (convert ng ng' gi))
      | (impr ng'  B g) =>
          (impr3 (B (convert ng ng' gi))
                 (b3' l ist nh hyp hi ng' g (convert ng ng' gi)))
      | orl ng' g B =>
          orl3 (b3' l ist nh hyp hi ng' g (convert ng ng' gi))
               (B (convert ng ng' gi))
      | orr ng' B g =>
          orr3  (B (convert ng ng' gi))
                (b3' l ist nh hyp hi ng' g (convert ng ng' gi))
      | andl ng' g B =>
          andl3 (b3' l ist nh hyp hi ng' g (convert ng ng' gi))
               (B (convert ng ng' gi))
      | andr ng' B g =>
          andr3  (B (convert ng ng' gi))
                 (b3' l ist nh hyp hi ng' g (convert ng ng' gi)) 
      |  (fa ng' s nv g) =>
               fa3 s nv (fun n=>
                  (b3' l ist nh hyp hi (cons s ng') g
                      (n, convert ng ng' gi))) 
      | ex ng' s nv g =>
          match ist with
          | cons (Some (existT sf (existT n1f (existT n2f ff)))) ist =>
              b3' l ist
                 nh hyp hi
                 (cons s ng') g
                 ((trs _ sf s (ff (convert nh _ hi)
                     (convert ng _ gi)))
                     ,
                   (convert ng ng' gi))
          |  cons None ist =>
               ex3 s nv
                 (fun p =>
                    b3' l ist nh hyp hi
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
           (b3' l ist nh' h (convert nh nh' hi)
                    ng goal gi)
      | andr nh' B h =>
                 (b3' l ist nh' h (convert nh nh' hi)
                     ng goal gi)
      | orl nh' h B =>
          andl3 (b3' l ist nh' h (convert nh nh' hi)
                   ng goal gi)
               ((B (convert nh nh' hi))->
                (coerce ng goal gi))
      | orr nh' B h =>
          andr3 ((B (convert nh nh' hi))->
                (coerce ng goal gi))
               (b3' l ist nh' h (convert nh nh' hi)
                   ng goal gi) 
      | impr nh' B h =>
          andr3 (B (convert nh nh' hi))
                (b3' l ist nh' h (convert nh nh' hi)
                   ng goal gi)
      | fa n s nv h =>
          match ist with
          | cons (Some (existT sf (existT n1f (existT n2f ff)))) ist =>
              (b3' l ist
                  (cons s n) h
                  (convert (cons sf nh)(cons s n)
                           (ff (convert nh _ hi)
                               (convert ng _ gi),
                             hi))
                  ng goal gi)

                  (*
                 nh hyp hi
                 (cons s ng') g
                 ((trs _ sf s (ff (convert nh _ hi)
                     (convert ng _ gi)))
                     ,
                   (convert ng ng' gi))

              (b3' l ist
                  (cons s n) h (convert
                         (cons s nh) (cons s n)
                         ((appist s f nh hi ng gi),hi))
                  ng goal gi) *)
          | cons None ist =>
              ex3 s nv
                  (fun p =>
                     (b3' l ist
                         (cons s n) h
                         (convert (cons s nh)(cons s n)
                                  (p, hi))
                         ng goal gi))
          | _ => bot3
          end
      | ex n s nv h =>
          fa3 s nv
            (fun p =>
               (b3' l ist
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
with f3' (l:trace)(ist: inst)(n1:ct)(h1 : cx n1)(i1 : pp n1)
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
                    (trs ts s1 s2 (t (convert n1 n1' i1)))))))
                  (P (convert (cons s2 n2)(cons s2 n2')
                             ((trs ts s1 s2 (u (convert n1 n1' i1))),
                               i2)))
          | _ => top3
          end
      | property n1' s1 P v =>
          match h2 with
         | equality n2' s2 t u =>
              impl3
                (Hol3 (s1 = s2 /\
                ((v (convert n1 n1' i1)  =
                    (trs ts s2 s1 (t (convert n2 n2' i2)))))))
                  (P (convert (cons s1 n1)(cons s1 n1')
                             ((trs ts s2 s1 (u (convert n2 n2' i2))),
                               i1)))
          | _ => top3
          end
      | andl n1' h1' B =>
          f3' l ist n1' h1' (convert n1 n1' i1) n2 h2 i2
      | andr n1' B h1' =>
          f3' l ist n1' h1' (convert n1 n1' i1) n2 h2 i2
     | orl  n1' h1' B =>
          orl3  (f3' l ist n1' h1' (convert n1 n1' i1) n2 h2 i2)
                (B (convert n1 n1' i1))
      | orr n1' B h1' =>
          orr3 (B (convert n1 n1' i1))
               (f3' l ist n1' h1' (convert n1 n1' i1) n2 h2 i2) 
      | impl n1' h1' B =>
          impl3 (b3' l ist n2 h2 i2 n1' h1'
                    (convert n1 n1' i1))
                (B (convert n1 n1' i1))
      | cNot n1' h1' =>
          not3
            (b3' l ist n2 h2 i2 n1' h1'
                (convert n1 n1' i1))
      | impr n1' B h1' =>
          impr3  (B (convert n1 n1' i1))
                 (f3' l ist n1' h1' (convert n1 n1' i1) n2 h2 i2)
      | fa n1' s1 nv h1' =>
          match ist with
            | cons None ist =>
                fa3 s1 nv (fun n =>
                    (f3' l ist (cons s1 n1') h1'
                        (convert (cons s1 n1)(cons s1 n1') (n, i1))
                        n2 h2 i2))
          | cons (Some (existT sf (existT n1f (existT n2f ff)))) ist =>
              (f3' l ist (cons s1 n1') h1'
                   (convert (cons sf _)  _
                            (ff (convert n1 _ i1)(convert n2 _ i2),
                   i2))  n2 h2 i2)

          | _ => top3
          end
      | ex n1' s1 nv h1' =>
          ex3 s1 nv
              (fun n =>
                 (f3' l ist (cons s1 n1') h1'
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
                         (trs ts s1 s2 (u (convert n1 n1' i1)))))))
               (P (convert (cons s2 n2)(cons s2 n2')
                            ((trs ts s1 s2 (t (convert n1 n1' i1))),
                              i2)))
          | _ => top3
          end
    
       | equality n2' s2 t u =>
           match h1 with
           | property n1' s1 P v =>
              impl3
                (Hol3 (s1=s2 /\
                     ((v (convert n1 n1' i1)=
                         (trs ts s2 s1 (u (convert n2 n2' i2)))))))
               (P (convert (cons s1 n1)(cons s1 n1')
                            ((trs ts s2 s1 (t (convert n2 n2' i2))),
                              i1)))

           |_ => top3
           end
      | andl n2' h2' B =>
          f3' l ist n1 h1 i1  n2' h2' (convert n2 n2' i2)
      | andr n2' B h2' =>
          f3' l ist n1 h1 i1 n2' h2' (convert n2 n2' i2)
     | orl  n2' h2' B =>
          orl3 
               (f3' l ist n1 h1 i1 n2' h2' (convert n2 n2' i2))
               (B (convert n2 n2' i2)) 
      | orr n2' B h2' =>
          orr3 (B (convert n2 n2' i2))
               (f3' l ist n1 h1 i1 n2' h2' (convert n2 n2' i2)) 
      | impl n2' h2' B =>
          impl3 (b3' l ist n1 h1 i1 n2' h2' (convert n2 n2' i2))
                (B (convert n2 n2' i2))
       | cNot n2' h2' =>
           not3
             (b3' l ist n1 h1 i1 n2' h2'
                 (convert n2 n2' i2))
      | impr n2' B h2' =>
          impr3  (B (convert n2 n2' i2))
                 (f3' l ist n1 h1 i1 n2' h2' (convert n2 n2' i2) )
       | fa n2' s2 nv h2' =>
          match ist with
            | cons None ist =>
                fa3 s2 nv (fun n =>
                 (f3' l ist n1 h1 i1
                     (cons s2 n2') h2'
                     (convert (cons s2 n2)(cons s2 n2') (n, i2))
                 )) 
          | cons (Some (existT sf (existT n1f (existT n2f ff)))) ist =>
              (f3' l ist n1 h1 i1
                   (cons s2 n2') h2'
                   
                  (convert (cons _ _)(cons s2 n2')
                           (ff (convert n1 _ i1)
                               (convert n2 _ i2),
                             i2)))
 
(*
              
              (f3' l ist n1 h1 i1
                  (cons s2 n2') h2'
                  (convert (cons s2 n2)(cons s2 n2')
                           ((appist s2 f n1 i1 n2 i2),i2))
                  )*)
          | _ => top3
         end
       | ex n2' s2 nv h2' =>
           ex3 s2 nv
               (fun n =>
                  (f3' l ist n1 h1 i1
                      (cons s2 n2') h2'
                   (convert (cons s2 n2)(cons s2 n2') (n, i2))
                 )) 
      | _ => top3
      end
  end   .

*)

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
       |nh' P h|nh' h P|s' nv nh' h|s' nv nh' h|nh' s' t u|nh' s' R t u|nh s' P v] //= hi
   [|sg ng]
   [ng'|ng'|ng' Q| ng' Q|ng' Q g|ng' g Q|ng' Q g|ng' g Q
       |ng' Q g|ng' g Q|sg' nv ng' g|sg' nv ng' g|ng' s'' t' u'|ng' s'' R' t' u'|ng' s'' P' v']
   gi //=;
   rewrite /= ?convert_corr ;
  try (by rewrite /= ?convert_corr ?ppce//=; move => [-> h2] e//=);
  try (by rewrite /= ?ppce ?convert_corr //=; eauto);
           move => [[e1 e2] p]//=; move: v' P' p e2; rewrite e1; move => v' P';
 rewrite ?trs_corr;
  try (by  move => p' <- <-);
  try (by move => p' <- ->);
 try  (move => p' [-> eqr] r; eapply eqr; [rewrite ?trs_corr; exact r| done]).

- move => [|] _ _
   [|s2 n2]
   [nh'|nh'|nh' P|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
       |nh' P h|nh' h P|s' nv nh' h|s' nv nh' h|nh' s' t u|nh' S' R t u |nh s' P v] //= hi
   [|sg ng]
   [ng'|ng'|ng' Q| ng' Q|ng' Q g|ng' g Q|ng' Q g|ng' g Q
       |ng' Q g|ng' g Q|sg' nv ng' g|sg' nv ng' g|ng' s'' t' u'|ng' S'' R' t' u' | ng' s'' P' v']
   gi //=;
   rewrite /= ?convert_corr ;
   try (by move => e1 p [e2 e3] //=;
          move: v' P' e3 p; rewrite -e2; move => v' P';
          rewrite ?trs_corr; move =>  -> p; rewrite e1);
   try (by move => p e1 [e2 e3]; move: u' t' e3 e1;
        rewrite -e2;
        move => u' t' ; rewrite !trs_corr; move => <- ->);

   try (by  move => <- p [e2 e3]; move: v' P' p e3;
        rewrite -e2;
        move => v' P' p  ; rewrite !trs_corr; move => <-);

   try (by move => p <- [e1 e2];
         move: {u'}  t' e2; rewrite -e1; move => t'; rewrite !trs_corr; move <-);
try(
  move => r p [es]; move: t u R r; rewrite es => t u R r [e eqr];


  eapply eqr; [rewrite ?trs_corr; exact r| rewrite trs_corr in e; rewrite -e; done]);
try  (move => r p [es]; move: t' u' R' p; rewrite -es => t u R p [e eqr]; eapply eqr;
    [ idtac| exact r];
rewrite trs_corr in e; rewrite !trs_corr; rewrite e; done).

- move => [|] b ist nh hyp hi ng
          [ng'|ng'|ng' Q|ng' Q|ng' Q g|ng' g Q|ng' Q g|ng' g Q
              |ng' Q g|ng' g Q|ng' nv' sg' g|ng' nv' sg' g
              |ng' sg' t u|ng' sg' R t u | ng' s P v] gi //=;
  rewrite /= ?ppce ?convert_corr //=; eauto;
  try (by move => [h|h]; eauto);
  try (by  move => [h1 h2]; split ; eauto).
  * case: ist => [//=|[f|] ist]; first by eauto.
    by move => [w hw]; eauto.
  * case: ist => [//=|[f|] ist]; first by eauto.
    by move => [w hw]; eauto.


 (* * induction hyp; rewrite //= convert_corr.
    move => [[ss e] p] tt.
    move: v  w w0 e tt p.
    by rewrite -ss => v t t0; rewrite !trs_corr => -> ->. *)

- move => fl [|] ist n1 h1 i1 n2 h2 i2 hr1 hr2.

   move: h1 i1 hr1 =>
        [nh'|nh'|nh' P|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
        |nh' P h|nh' h P|nh' s nw h|nh' s nw h|nh' s t u|
        |nh' s P v] //= P1 i1;
      rewrite ?convert_corr; eauto;
   try (by case: i1; eauto);
  move: P1 i1 hr2 => i1 pv;
    try (by case:  ist => [|[f|] ist] //=; eauto);
    try (by move: IHh2; case:  ist => [|[f|] ist] //=; eauto);
    try (by case: pv => [p hp] c; exists p;
         eapply hl2; auto; rewrite trs_corr; auto).
 
 move: h2 i2 hr2 =>
        [nh'|nh'|nh' P|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
        |nh' P h|nh' h P|nh' s nw h|nh' s nw h|nh' s t u|nh' s R t u
        |nh' s P v] //= P2 i2;
      rewrite ?convert_corr; eauto;
   try (by case: i2; eauto);
  move: P2 i2 hr1 => i2 pv;
  induction h1; try done;
    try (by case:  ist => [|[f|] ist] //=; eauto);
    try (by move: IHh1; case:  ist => [|[f|] ist] //=; eauto);
    try (by case: pv => [p hp] c; exists p;
         eapply hl2; auto; rewrite trs_corr; auto).


(*
move => fl h [e1 e2].
rewrite trs_corr.
move:  t u pv w  e2 h.  
rewrite -e1.
move => h1 h2 s1 s2.

rewrite !trs_corr convert_corr s1.
simpl. by move <-.
  by rewrite /= convert_corr; move => [e1  [e3 e2]];
      rewrite trs_corr e1 -e2. *)

- move => fl b ist nh
          [nh'|nh'|nh' P|nh' P|nh' P h|nh' h P|nh' P h|nh' h P
              |nh' P h|nh' h P|nh' s nv h|nh' s nv h|nh' s t u|nh' s R t u
              |nh' s P v] i1 //=;
   rewrite ?convert_corr ?ppce  ?trs_corr //= => ng goal gi;
   try (by intuition; eauto).

case: ist => [//=|[f|] ist]; first by eauto.
  move => [p hp]; eauto.
  move => hh [w hw]; apply (hl1 fl b ist (s::nh') h (w,i1)); eauto.
     by move: (hh w); rewrite trs_corr.

(*   induction goal; try done; move => /= [[e h2] h3] h4.
  move: P w h2 h3 h4 ; rewrite -e ?trs_corr => P t0.
  rewrite trs_corr convert_corr => <- p -> //=. *)
- move => fl [|] ist n1.


move => h1 i1 n2  [nh'|nh'|nh' P|nh' P|nh' P h|nh' h P|nh' P h
              |nh' h P|nh' P h|nh' h P|nh' s nw h|nh' s nw h
                  |nh' s t u|nh' s R t u|nh' s P v] /= i2 p1 p2 //=;
             rewrite ?convert_corr; try (by intuition; eauto).
  case: ist =>[//=|[f|] ist]; eauto; move => p; eauto.
  move: p2 => [p2 hp]; exists p2; rewrite trs_corr; eauto.


 move =>
  [nh'|nh'|nh' P|nh' P|nh' P h|nh' h P|nh' P h
              |nh' h P|nh' P h|nh' h P|nh' s nw h|nh' s nw h
              |nh' s t u|nh' s R t u|nh' s P v] /= 
         i1 n2 h2 i2 p1 p2 //=;
  rewrite ?convert_corr; try (by intuition; eauto).
     case: ist =>[//=|[f|] ist]; eauto; move => p; eauto.
     move: p1 => [p1 hp]; exists p1; rewrite trs_corr; eauto.
Qed.
  
(* induction h2; try done.
 rewrite /=; move => [e1 e2]; move: e2 p2.
 rewrite /=  trs_corr convert_corr.
 move: i1 p1 P w; rewrite -e1; move => i1 -> P s1.
 rewrite trs_corr.
by move ->.  

  induction h2; try done.
move => [e1 e2].
rewrite trs_corr.
move: w w0 e2 p2 p1.  
rewrite -e1.
move => s1 s2; rewrite !trs_corr convert_corr.
by move => -> ->. *)

Definition trl3 := nosimpl tr3.


(* The two actually used corollaries *)
Lemma b3_corr : 
    (forall (fl:bool) (l:trace) b  (ist : inst') (nh : ct)  (hi : pp nh)
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
  forall (fl:bool) (l: trace) b (ist : inst') (n1 : ct) (h1 : cx n1) (i1 : pp n1) 
         (n2 : ct) (h2 : cx n2) (i2 : pp n2),
    coerce n1 h1 i1 ->
    coerce n2 h2 i2 ->
    trl3 (f3 fl l b ist n1 h1 i1 n2 h2 i2).
move => fl l b ist n1 h1 i1 n2 h2 i2.
case: (bf3_corr l) => [_ h]; apply h.
Qed.

(* The function instantiating an inner quantifier *)
Fixpoint instp (t:nat)(s : nat)(o : wsort ts s)(n : seq nat)
         (c : pp n)(h : cx n) : Prop :=
  match t with
  | 0 =>
      match h with
      | fa n' s' _ h' =>
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
      | fa n' s' _ h' =>
          forall x : wsort ts s',
            ( instp t s o (s'::n') (convert (s'::n)(s'::n') (x,c)) h')
     | ex n' s' _ h' =>
          exists x : wsort ts s',
            ( instp t s o (s'::n') (convert (s'::n)(s'::n') (x,c)) h')
      | X => True
      end
  end
with
instn (t:nat)(s : nat)(o : wsort ts s)(n : seq nat)
         (c : pp n)(h : cx n) : Prop :=
  match t with
  | 0 =>
      match h with
      | ex n' s' _ h' =>
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
      | fa n' s' _ h' =>
          forall x : wsort ts s',
            ( instn t s o (s'::n') (convert (s'::n)(s'::n') (x,c)) h')
      | ex n' s' _ h' =>
          exists x : wsort ts s',
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
            n' Q h'|n' h' Q| n' s' nv h'|n' s' nv h'|
            n' s' t1 t2 | n' s' R t1 t2 | n' s' Q t1] c;
          split; try (simpl; rewrite ?ppce; done);
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


Ltac dmDYN T :=
  match T with
  | Prop => constr:(mDYN Prop True)
  | _ =>   
  constr:(mDYN T ltac:((try constructor);
                       (trivial; fail);
                       (try exact True);
                       auto))
  end.

Ltac defDYN T :=
  let d := dmDYN T in
  match d with
  | mDYN _ ?t => constr:(t)
  end.

Ltac lmDYN l :=
  let lh := eval hnf in l in
    match lh with
    | nil => constr:(@nil DYN)
    | cons ?T ?l' =>
        let d := dmDYN T in
        let r := lmDYN l' in
        constr:(@cons DYN d r)
    end.

Ltac tmDYN l :=
  let lh := eval hnf in l in
    match lh with
    | nil => constr:(@nil DYN)
    | cons (tDYN ?T) ?l' =>
        let d := dmDYN T in
        let r := tmDYN l' in
        constr:(@cons DYN d r)
    end.

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

Fixpoint strip l :=
  match l with
  | nil => nil
  | cons (mDYN T _) l => cons (tDYN T) (strip l)
  end.

Definition trr : forall ts n, sort (strip ts) n -> wsort ts n.
elim => [|[T a] ts rts] [|n]//=.
exact (rts n).
Defined.

Definition trr_inv : forall ts n, wsort ts n -> sort (strip ts) n.
elim => [|[T a] ts rts] [|n]//=.
exact (rts n).
Defined.


Definition env (ts : tls) := forall s : nat, nat -> sort ts s.

Definition inst1 (ts : tls) :=
  {s : nat & env ts -> env ts -> sort ts s}.

Definition srestrip :
  forall ts, (inst1 (strip ts)) -> (inst2 ts).
move => ts [s f]; exists s.
move => e1 e2.
apply trr.
apply f; clear s f.
move => s n; apply trr_inv; apply e1; exact n.
move => s n; apply trr_inv; apply e2; exact n.
Defined.

Fixpoint restrip ts l :=
  match l with
  | nil => nil
  | cons None l => cons None (restrip ts l)
  | cons (Some f) l => cons (Some (srestrip ts f)) (restrip ts l)
  end.

Notation "'subst!' y 'for' x 'in' f" :=
 (match y with x => f end) (at level 10, f at level 200).

Ltac beta1 func arg :=
 lazymatch func with
 | (fun a => ?f) => constr:(subst! arg for a in f)
 end.

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
                     orename constr:(f (def ts s))
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
                     orename constr:(f (def ts s))
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
          let u := simpl_path_r
                     p'
                     ltac:(extract ltac:(tnth l (S n))) in
          let l' := ttreplace constr:(mDYN _ u) (S n) l in
          let r := rebuild l'
          in r
      end
  end.

Ltac simpl_path p :=
  match goal with
  | |- ?g =>
      let g' := simpl_path_r p g in
      change g'
  end;
  simplify_goal.


Ltac simpl_path_hyp h p :=
  let g := type of h in
  let g' := simpl_path_r p g in
  change g' in h;
  simplify_hyp h.

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
  | cons  (mDYN U _) ?y  => constr:(n)
  | cons  _ ?l1  => st_aux constr:(S n) l1 T
  end.

Ltac tst ts T :=
  (st_aux constr:(0) constr:(ts) T). 

(* Definition IDT := fun X:Type => X. *)


Inductive listn :=
  niln | consn : nat -> listn -> listn.
Definition test := (cons  (mDYN nat 0)
                        (cons (mDYN bool true)
                              (cons (mDYN Prop True)
                   (cons (mDYN listn niln) nil)))).

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

                
(*
Parameter f : nat -> nat -> nat -> nat.
Parameter R : nat -> nat -> Prop.
Check ltac:( let r := 
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
 (*    | forall x: (wsort _ ?s), @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: (wsort ts s) => ltac:(
           let body := beta1 body' y in
              let r := reify_rec ts l' (cons s n) (cons (mDYN (wsort ts s) y) env) body in
              exact r))
           with
        | (fun _: (wsort ts s) => ?r) => constr:(fa ts n s (fun x:nat=>x) r) 
        end *)

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
              let r := reify_rec ts l' (cons s n) (cons (mDYN a y) env) b in
              exact r))
     with
     | (fun _: a => ?r) => constr:(fa ts n ltac:(let s := tst ts a in exact s) (fun x:nat=>x) r) 
     end
     end
      | forall x: ?T, @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: T => ltac:(
           let body := beta1 body' y in
           let s := ltac:( tst ts T) in                                  
              let r := reify_rec ts l' (cons s n) (cons (mDYN T y) env) body in
              exact r))
     with
     | (fun _: T => ?r) => constr:(fa ts n ltac:(let s := tst ts T in exact s) (fun x:nat=>x) r) 
     end
      | exists x: ?T, @?body' x =>
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

Definition t := forall z x, x = 2 /\ z = true.
Definition cct :=
  ltac:(let r :=
          reify_rec test
                    (cons false (cons false (cons false nil))) (@nil nat)
                    (@nil DYN)
                    (forall z x, x = 2 /\ z = true)  in exact r).



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


Lemma magic : forall l1 i l2 l3,
    l1 = l2 ++ l3 ->
    wsort l2 i -> wsort l1 i.
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


(*Check ltac:(let r := fetch_def Prop constr:(test)
            in exact r).*)
(* TODO : blinder pour éviter les confusions forall implication *)
Ltac mkSign l p t :=
  match p with
  | nil =>
      match t with
      | (@eq ?T _ _) => aDYN T l
      | _ => l
      end
  | cons false ?p =>
      match t with
      | ?a /\ ?b => mkSign l p a
      | ?a \/ ?b => mkSign l p a
      | ?a -> ?b => mkSign l p a
      | ~ ?a => mkSign l p a
      | forall x : ?T, ?body =>
          let l' := aDYN T l in
          let d := defDYN T  in
          mkSign l' p (subst! d for x in body)
      |  exists x : ?T, ?body =>
          let l' := aDYN T l in
          let d := defDYN T in
          mkSign l' p (subst! d for x in body)
      end
  | cons true ?p =>
      match t with
      | ?a /\ ?b => mkSign l p b
      | ?a \/ ?b => mkSign l p b
      | ?a -> ?b => mkSign l p b
  end
end.

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



(* same but detecting True and False *)

Ltac reify_rec_at ts' l n env t :=
  let z := fresh "z" in
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

       | forall x: (wsort _ ?s), @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: (wsort s) => ltac:(
           let body := beta1 body' y in
              let r := reify_rec_at ts l' (cons s n) (cons (mDYN (wsort ts s) y) env) body in
              exact r))
     with
     | (fun _: (wsort ts s) => ?r) => constr:(fa ts n s r) 
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
           let r := reify_rec_at ts l' (cons s n) (cons (mDYN a y) env) b in
           exact r))
  with
  | (fun _: a => ?r) => constr:(fa ts n ltac:(let s := tst ts a in exact s) r) 
  end end
      | forall x: ?T, @?body' x =>
          let y := fresh "y" in
          lazymatch constr:(fun y: T => ltac:(
           let body := beta1 body' y in
           let s := ltac:(tst ts T) in                                  
              let r := reify_rec_at ts l' (cons s n) (cons (mDYN T y) env) body in
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
                               n) (cons  (mDYN T y) env) body in
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
     let r := reify_rec ts l  (@nil nat)  (@nil DYN)  g in
     change (coerce ts (@nil nat) r tt)
 end.

Ltac reify_goal_at ts l :=
 lazymatch goal with
 | |- ?g =>
     let r := reify_rec_at ts l (@nil nat)  (@nil DYN) g in change (coerce ts (@nil nat) r tt)
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
  let tsw := tmDYN ts in
  let x := fresh "x" in
  move: (h) => x;
               reify_hyp tsw l x;
  let sy := type of x in
   match sy with
   | coerce _ (@nil nat) ?hc _ =>
       move: (instp_corr tsw  (pred (length l))  s o (@nil nat) hc tt h) => h';
       rewrite /= ?trs_corr in h';
       rewrite /trs /eqnqtdec /eq_rect_r /eq_rect /nat_rec /eq_sym  /nat_rect /wsort in h';
       clear x
   end;
   try discriminate.

Ltac inst_hyp_nd ts l h s o :=
  let ts' := tmDYN ts in
  reify_hyp ts' l h;
  let sy := type of h in
   match sy with
   | coerce (@nil nat) ?hc _ =>
       move: (instp_corr ts' (pred (length l))  s o (@nil nat) hc tt h);
       clear h; move => h;
       rewrite /= ?trs_corr in h;
        rewrite /trs /eqnqtdec /eq_rect_r /eq_rect /nat_rec /eq_sym  /nat_rect /wsort /sl  in h
   end;
   try discriminate.

(*
   Goal (forall X :  Prop,  X) -> False.
intro h.



inst_hyp_nd test (cons false nil) h 2 ( False).
by apply h.
Abort. *)




Ltac inst_goal ts' l s o :=
  let ts := tmDYN ts' in
  reify_goal ts l;
   match goal with
   | |- coerce _ (@nil nat) ?hc _ =>
      apply (instn_corr ts (pred (length l))  s o (@nil nat) hc tt);
       rewrite /= ?trs_corr
   end;
  try discriminate.
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

Ltac back_o ts' h0 hp gp t i :=
  let ts1 := eval hnf in ts' in
    let ts := fresh "ts" in
    pose ts := ts1;
  let h := fresh "h" in
  move: (h0) => h;
  reify_goal ts gp;
  reify_hyp ts hp h;
  let o := type of h in
  match o with
    | coerce _ (@nil nat) ?hc _ =>
        apply (b3_corr ts true t false i (@nil nat) tt (@nil nat) tt hc);
        [idtac|assumption];
        (apply trex_norm_apply; [simpl; try done; auto|
                                  (*  rewrite ?/ts /trad /trad1 /b3 /o3_norm /coerce ; *)
       try exact tt];
         let sq :=
           match goal with
           | |- trl3 _ ?o => o
           end
         in
         rewrite   /b3 /o3_norm /trl3 /convert /coerce /xor /appist /switch_inst2 /trad1 /nths   /trs /tr3 /eqnqtdec /nat_rec /nat_rect /eq_rect_r /eq_rect  /eq_ind_r /eq_ind  /eq_sym /list_rect /ts  /wsort /sl;
         let tt :=
           match goal with
           | |- ?tt => tt
           end
         in
         let nt := orename sq tt
         in try change nt;
         simplify_goal
        );
        try by apply I;
        try discriminate
  end;
  try clear h; try clear ts.

Ltac back ts h0 hp gp t i :=
  let tsw := tmDYN ts in
  let iw1 := constr:(restrip tsw i) in
  let iw2 := eval hnf in iw1 in
  let iw := eval simpl in iw2 in

  back_o tsw h0 hp gp t iw.

(*  let th := type of h0 in
  let ts'' := mkSign ts''' hp th in 
  match goal with
  | |- ?g =>
      let ts := mkSign ts'' gp g in
      back_o ts' h0 hp gp t i
  end. *)


(*
Parameter A : Prop.
Print test.
Goal A -> forall x:nat,A/\A.
  intro a.
  back [:: mDYN nat 0; mDYN bool true; mDYN Prop True;
    mDYN listn niln]
       a (@nil bool)(cons false (cons false nil))(cons true (cons true nil))(@nil (option (inst2 test))).  
rewrite /test. *)
  
(* rewrite with hypothesis h in goal 
 hp : list bool = path to the equality
 gp : list bool = path to the atomic proposition containing the term
 gp' : list nat = path to the term
 t : list bool = trace (with the last bool for choice l <-> r)
 i : instantiation *)

Ltac rew_dnd_o ts' h hp gp gp' t i :=
  let fl := get_last t in
  let t' := snitch_last t in
  let tsc := eval compute in ts' in
  let ts := fresh "ts" in
  pose ts := tsc; 
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
  apply (b3_corr ts fl t' false i  (@nil nat) tt (@nil nat) tt
                 ec gc);
  [idtac| assumption];
  (apply trex_norm_apply ; [split; try reflexivity|idtac]);
  try clear h';
  try(
  let os :=
    match goal with
    | |- trl3 _ ?o => o
    end
  in
  rewrite   /b3 /trl3 /o3_norm /coerce /convert /xor /appist /switch_inst2 /trad1 /nths   /trs /tr3 /eqnqtdec /nat_rec /nat_rect /magic  /magic_inst2 /magic /list_rect
            /eq_rect_r /eq_rect /eq_sym /f_equal  /eq_ind_r /eq_ind  /eq_sym
            
  /ts;
  match goal with
  | |- ?tt =>
      let nt := orename os tt in
      try
        change nt
  end);
    simplify_goal;


  (*
rewrite ?/ts /coerce /b3 /trl3 /tr3 /o3_norm ?trs_corr /convert  /defs /appist ?trs_corr;
     rewrite  /coerce /b3 /trl3 /tr3 /o3_norm ?trs_corr /convert /cT /cB  /appist /wsort /trad1 /nthc /list_rect /wsort /sl;
  rewrite ?trs_corr /trs ?eqnqtdec_refl /eq_rect_r /eq_rect /Logic.eq_sym; 
  simplify_goal; *)
  rewrite  /wsort /sl; try clear ts.


Ltac rew_dnd_oo ts' h hp gp gp' t i :=
  let tsw := tmDYN ts' in
  let iw1 := constr:(restrip tsw i) in
  let iw2 := eval hnf in iw1 in
  let iw := eval simpl in iw2 in

  rew_dnd_o tsw h hp gp gp' t iw.

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
  apply (b3_corr ts fl t' false i  (@nil nat) tt (@nil nat) tt
                 ec gc);
  [idtac| assumption];
  (apply trex_norm_apply ; [split; try reflexivity|idtac]);
  try clear h';
  try(
  let os :=
    match goal with
    | |- trl3 _ ?o => o
    end
  in
  rewrite   /b3 /trl3 /o3_norm /coerce /convert /xor /appist /switch_inst2 /trad1 /nths   /trs /tr3 /eqnqtdec /nat_rec /nat_rect /magic  /magic_inst2 /magic /list_rect
            /eq_rect_r /eq_rect /eq_sym /f_equal  /eq_ind_r /eq_ind  /eq_sym
            
  /ts;
  match goal with
  | |- ?tt =>
      let nt := orename os tt in
      try
        change nt
  end);
    simplify_goal;
  rewrite  /wsort /sl; try clear ts.


Ltac rew_dnd_rev ts' h hp hp' gp t i :=
  let tsw := tmDYN ts' in
  let iw1 := constr:(restrip tsw i) in
  let iw2 := eval hnf in iw1 in
  let iw := eval simpl in iw2 in
  rew_dnd_rev_o tsw h hp hp' gp t iw.

Ltac rew_dnd ts' h hp gp gp' t i :=
  (rew_dnd_oo ts' h hp gp gp' t i) +
    (rew_dnd_rev ts' h gp gp' hp t i).


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
(*  match (fl) with
  | false =>
      move:
      (f3_corr ts flt t' i' (@nil nat) hc1 tt
               (@nil nat) hc2 tt h1 h2) => h4
  | true => *)
   let nfl := eval hnf in (negb fl) in
     let i' := eval simpl in
     (if fl then i
                   else (switch_inst _ i)) in 
      move:
    (f3_corr ts flt t' nfl
                       i' (@nil nat) hc2 tt
               (@nil nat) hc1 tt h2 h1) => h4
(*  end *) ;
  let oh4 :=
    match type of h4 with
    | (trl3 _ ?oh) => oh
    end in
  cut (trex ts oh4); [idtac| by split];
  move => h5;
  move: (trex_norm_fapply ts oh4 h5 h4) => h3;
  try clear h5; try clear h4;
  let st :=
    match type of h3 with
    | trl3 _ ?oh => oh
    end in
  rewrite /f3 /trl3 /o3_norm /convert /coerce /xor /appist /switch_inst2 /trad1 /nths   /trs /tr3 /eqnqtdec /nat_rec /nat_rect /eq_rect_r /eq_rect  /eq_ind_r /eq_ind  /eq_sym /list_rect /ts  /wsort /sl in h3;
  let np := type of h3 in
  let nnp := orename st np in
  try change nnp;
 (*    rewrite ?/ts /coerce /wsort /trl3 /tr3 /f3 /o3_norm /cT /cB in h3;
   rewrite /convert /trs ?eqnqtdec_refl /eq_rect_r /eq_rect /Logic.eq_sym in h3;
   rewrite /appist /trs /eqnqtdec /eq_rect_r /eq_rect /nat_rec /nat_rect /protect_term  /eq_ind_r /eq_ind /eq_sym /f_equal /wsort /sl in h3; *)
   try clear ts;
  simplify_hyp h3;
try discriminate.



Ltac rew_dnd_hyp ts' fl  h1 h2 h3 hp1 hp2 hp2' t i :=
  let tshn := eval hnf in ts' in
    let tsw := tmDYN tshn in
    let ts'' := eval simpl in tsw in
    let iw1 := constr:(restrip tsw i) in
    let iw2 := eval hnf in iw1 in
    let iw := eval simpl in iw2 in

      rew_dnd_hyp_o tsw fl  h1 h2 h3 hp1 hp2 hp2' t iw.
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
           move:
           (f3_corr ts true  t false i (@nil nat) hc1 tt
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
    rewrite /f3 /trl3 /o3_norm /convert /coerce /xor /appist /switch_inst2 /trad1 /nths /trs /tr3 /eqnqtdec /nat_rec /nat_rect /eq_rect_r /eq_rect  /eq_ind_r /eq_ind  /eq_sym /list_rect /ts /wsort /sl in h3;
    let np := type of h3 in
    let nnp := orename st np in
    try change nnp in h3;
    simplify_hyp h3;
  try clear ts;
    try discriminate.

Ltac forward ts' h1' h2' h3 hp1 hp2 t i :=
  let tsw := tmDYN ts' in
  let iw1 := constr:(restrip tsw i) in
  let iw2 := eval hnf in iw1 in
    let iw := eval simpl in iw2 in
    forward_o tsw h1' h2' h3 hp1 hp2 t iw.
(*
  let th1 := type of h1' in
  let th2 := type of h2' in
  let ts'' := mkSign tsw hp1 th1 in
  let ts := mkSign ts'' hp2 th2 in
  forward_o ts' h1' h2' h3 hp1 hp2 t i.
*)

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

(*Check ltac:(let r := ttest    (forall x : nat, forall y, x = y)
in exact r).*)

              
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
