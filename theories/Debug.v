From Actema Require Import Loader.
Require Import ssreflect.

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
  back h (cons false nil)(@nil bool)(cons false nil)
       (cons (Some instc2) nil).
Undo.
Fail actema_force.
Abort.


Goal 2=3 -> (exists x : nat, x = 3).
  intro h.
  back h (@nil bool)(cons false nil)(cons true nil)
       (cons (Some instc2) nil).
  Undo.
  Fail actema_force.
Abort.

Definition instremap : inst1.
exists 0.
intros f1 f2.
apply f1.
exact 0.
Defined.

Goal (exists x : nat, x = 3) -> (exists x : nat, x = 3).
intro h.
back h (cons false nil)(cons false nil)(cons false (cons true nil))
     (cons (Some instremap) nil).
Undo.
actema_force.
Abort.


Goal  (exists x : nat, x = 3)-> (exists (x:nat) y, x = y).
  intro h.
  back h (cons false nil)(cons false (cons false nil))
     (cons false (cons true (cons true nil)))
     (cons (Some instremap) (cons (Some instc3) nil)).
Undo.
Fail actema_force.  
Abort.
