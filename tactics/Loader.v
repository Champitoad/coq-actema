(* This is the module that the users of Actema have to [Require Import]
   to get access to the actema tactic. *)

Declare ML Module "coq-actema.plugin".

(* We do not Import Ltac2 as it would set the default proof mode to Ltac2. 
   We do however need to Require it in order to call Ltac2 tactics from Ocaml. *)
From Ltac2 Require Ltac2.

(* Export some modules so that we can call the Ltac2 functions they define
   from Ocaml tactics. *)
From Actema Require Export HOL.
From Actema Require Export DnD.
From Actema Require Export Misc.
From Actema Require Export Utils.