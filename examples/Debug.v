From Actema Require Import Loader.
Require Import ssreflect.

Parameter P : nat -> Prop.
Lemma bug3 (e : 4 = 4) : exists x, P x.
actema.
