From Actema Require Import Loader.
Require Import ssreflect.

Parameter f g : nat -> nat.
Lemma bug1 (e : (f 0) = 0) :
   f (g 0) = 0.
actema_force.


   (* ici on ne peut pas réécrire la 1e occurence de x avec e, alors que la tactique suivante marche : *)
   rew_dnd e
    (@nil nat)
    (cons 0 (cons 1 (cons 1 (cons 1 nil))))
    (cons true nil)
    (@nil (option DYN)).

Lemma exfa_faex (R : nat -> nat -> Prop) :
(exists x, forall y, R x y) -> (forall a, exists b, R b a).
Proof.
intro h.
back 
 h
 (1 :: 1 :: nil)%list
 (1 :: 1 :: nil)%list
 (true :: false :: true :: false :: nil)%list
 (Some (mDYN (nat -> nat -> nat) (fun x a : nat => x))
 :: Some (mDYN (nat -> nat -> nat -> nat) (fun x a b : nat => b)) :: nil)%list
.

actema_force. 

Lemma test (a : forall y : nat, forall z : nat, A /\ y = z) : forall x : nat, (A /\ B) \/ (A /\ x = 0 + x ).
actema_force.

(* [get_subterm path term] gets the subterm at path [path] of the Coq term [term].
   [path] is a list of nat. 
   This fails if the subterm depends on a variable bound above it in [term]. *)
(*Ltac get_subterm_r path term :=
  match constr:(pair path term) with
  (* Base case. *)
  | (nil, _) => constr:(term)
  (* Lambda. *)
  | (cons 0 ?p', fun x : ?T => ?body) => get_subterm_r p' T
  | (cons 1 ?p', fun x : ?T => @?body x) => 
      lazymatch
        constr:(fun x : T =>
           ltac:(let body := beta1 body x in
                 let r := get_subterm_r p' body in exact r))
      with                    
      | (fun _ : _ => ?res) => res
      end
  (* Dependent product. *)
  | (cons 0 ?p', forall x : ?T, ?body) => get_subterm_r p' T
  | (cons 1 ?p', forall x : ?T, @?body x) => 
      lazymatch
        constr:(fun x : T =>
           ltac:(let body := beta1 body x in
                 let r := get_subterm_r p' body in exact r))
      with                    
      | (fun _ : _ => ?res) => res
      end
  (* Existential quantification. *)
  | (cons 0 ?p', exists x : ?T, ?body) => get_subterm_r p' T
  | (cons 1 ?p', exists x : ?T, @?body x) => 
      lazymatch
        constr:(fun x : T =>
           ltac:(let body := beta1 body x in
                 let r := get_subterm_r p' body in exact r))
      with                    
      | (fun _ : _ => ?res) => res
      end
  (* Application. *)
  | (cons 0 ?p', ?f ?x) => get_subterm_r p' f
  | (cons 1 ?p', ?f ?x) => get_subterm_r p' x
  end.
     
Ltac myinduction path :=
  match goal with
  | |- ?g =>
      let subterm := get_subterm_r path g in
      pose (the_subterm := subterm) ;
      induction subterm
  end.

Definition f := fun x => x + 1 = 3.

Lemma test y : exists x : nat, f (x + y).
  myinduction (cons 1 (cons 1 (cons 1 nil))).
*)