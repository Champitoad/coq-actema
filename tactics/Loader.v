Declare ML Module "coq-actema.plugin".

(* We do not Import Ltac2 as it would set the default proof mode to Ltac2. 
   We do however need to Require it in order to call Ltac2 tactics from Ocaml. *)
From Ltac2 Require Ltac2.

From Actema Require Export HOL.
From Actema Require Export HOL2.