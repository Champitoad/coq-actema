From Actema Require Import Loader.
Require Import ssreflect.

About iff.

Definition x := 3.

About plus.

Inductive nlist := 
  | nnil : nlist
  | ncons : nat -> nlist -> nlist.

Definition target_const (l : nlist) : l = ncons 42 nnil. Admitted.

Lemma test_ : True.
  test.
Admitted.

Check mathcomp.ssreflect.eqtype.option_eqType.

Definition instc2 : inst1.
exists 0.
move => _ _; exact 2.
Defined.

Definition instc3 : inst1.
exists 0.
move => _ _; exact 3.
Defined.


Goal (forall x : nat, x = 3) -> 2 = 3.
  intro h.
  Set Printing All.
  back h (cons false nil)(@nil bool)(cons false nil)
       (cons (Some instc2) nil).
Undo.
actema.
Abort.

Goal 2=3 -> (exists x : nat, x = 3).
  intro h.
  back h (@nil bool)(cons false nil)(cons true nil)
       (cons (Some instc2) nil).
  Undo.
  actema.
Abort.

Definition instremap : inst1.
exists 0.
intros f1 f2.
apply f1.
exact 0.
Defined.

Goal (exists x : nat, x = 3) -> (exists y : nat, y = 3).
intro h.
back h (cons false nil)(cons false nil)(cons false (cons true nil))
     (cons (Some instremap) nil).
Undo.
actema.
Abort.


Goal  (exists x : nat, x = 3)-> (exists (x:nat) y, x = y).
  intro h.
  back h (cons false nil)(cons false (cons false nil))
     (cons false (cons true (cons true nil)))
     (cons (Some instremap) (cons (Some instc3) nil)).
Undo.
actema.  
Abort.
