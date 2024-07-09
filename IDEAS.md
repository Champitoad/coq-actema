# Improve lemma search performance

- most time is probably spent on unification (check ?).
- add a basic unification test, faster but which rejects less programs
  (e.g. without dealing with unification variables) to be performed before real unification.

# Fix lemma order in the UI list

- have a deterministic order (e.g. sort alphabetically on lemma name).
- add a priority system. e.g. :
  - most recent lemmas first.
  - compute a matching degree, which could be the size of the subterm of the lemma that matches 
    the current selection (better measure than size of the permutation).

# Topics for the report 

- Talk about the pretty-printer (it's a GADT).
- Talk about the lemma search "fast" unification.
- Unification : describe the problem formally and the solution.

# Problematic inputs for the backtracking unif algorithm : 

forall ?a ?b ?x1 ... ?xn : Prop, {a /\ x1 ... xn /\ ~ b}
=?=
forall ?c ?y1 ... ?yn : Prop, {c /\ y1 ... yn /\ c}

If we initially choose a := c, it won't work at the end because we will have a := f b which
violates the constraint that a can't depend on b.
We have to backtrack all the way up to the first assignment and choose c := a instead (and it still does not work, but it has to test every possibility first).

# Formalizing the unification algorithm

Define a judgement in the style of :
  A Unification Algorithm for COQ Featuring Universe Polymorphism and Overloading, Ziliani & Sozeau

We will also need an aliasing relation on metavariables. 

# Scratch

back :: hyp -> concl -> new_concl * proof
  where proof :: hyp -> new_concl -> concl

forward :: hyp1 -> hyp2 -> new_hyp * proof 
  where proof :: hyp1 -> hyp2 -> new_hyp

back A B when A = B
  new_concl := True 
  proof a _ := a

back (B /\ C) A 
  let D, (p :: B -> D -> A) := back B A
  new_concl := D
  proof (b, c) d := p b d

back A (B /\ C) 
  let D, (p :: A -> D -> B) := back A B
  new_concl := D /\ C
  proof a (d, c) := (p a d, c)

back (B \/ C) A 
  let D, (p :: B -> D -> A) := back B A
  new_concl := D /\ C -> A
  proof (inl b) (d, ca) := p b d
  proof (inr c) (d, ca) := ca c

back A (B -> C)
  let D, (p :: A -> B -> D) := forward A B
  new_concl := D -> C
  proof a dc := fun b => dc (p a b)

back (exists x, B x) A
  let ?x := new metavariable of the type of x.
  let D, (p :: B ?x -> D -> A) := back (B ?x) A
  -- ?x can appear in D and p

  new_concl := forall x, D[?x:=x]
  proof (ex x0 bx0) xd :: A := p[?x:=x0] bx0 (xd x0)
    where bx0 :: B x0
          xd :: forall x, D[?x:=x]
  -- works because when applying p we instantiate ?x by x0 in both p and D

back (forall x, B x) A (None :: ws)
  let ?x := new metavariable of the type of x.
  let D, (p :: B ?x -> D -> A) := back (B ?x) A (List.map (fun w -> w ?x) ws)
  -- ?x can appear in D and p

  new_concl := exists x, D[?x:=x] -- here we DON'T instantiate ?x, 
                                  -- we simply replace its occurences in D by x
  proof xb (ex x0 dx0) :: A := p[?x:=x0] (xb x0) dx0 -- here we DO instantiate ?x by x0
    where xb :: forall x, B x
          dx0 :: D[?x:=x0] -- here we DON'T instantiate ?x

back (forall x, B x) A (Some wx :: ws) 
  let D, (p :: B wx -> D -> A) := back (B wx) A (List.map (fun w -> w wx) ws)
                                                -- this part depends on whether we make the witnesses 
                                                -- in ws depend on wx or not. 
  new_concl := D
  proof xb d :: A := p (xb wx) d 
    where xb :: forall x, B x