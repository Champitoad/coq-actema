From Ltac2 Require Import Ltac2 Printf.
From Actema Require Import Utils.

(* When two formulas interact [A |- B] or [A * B],
   [A] is on the [Left] side and [B] is on the [Right] side. *)
Ltac2 Type side := 
  [ Left | Right ].

(* A choice of rule to apply. *)
Ltac2 Type choice := 
  [ (* Apply the next non-binder rule on the given side. *)
    Side (side) 
  | (* Apply the next binder rule on the given side. 
       The option contains an instantiation witness :
       - [None] means that the binder is not instantiated.
       - [Some witness] means that the binder is instantiated with [witness], 
         which is a closed term which binds all variables bound above (in the interleaved order). *)
    Binder (side, constr option) 
  ].

Ltac2 Type exn ::= [ InteractFailure ].


Ltac2 rec back 
  (h : constr) 
  (subh : int list) 
  (c : constr) 
  (subc : int list) 
  (choices : choice list) 
  : constr * constr 
:= 
  (* Put the two terms in head normal form. *)
  let h := eval hnf in $h in 
  let c := eval hnf in $c in 
  (* Print the link. *)
  printf "Backward : %t |- %t" h c;
  match choices, subh, subc with
  (* End rule : check [h] and [c] are beta equivalent. *)
  | [], [], [] => 
    if beta_equiv h c then 
      let d' := 'True in 
      let p' := '(fun (h_ : $h) (_ : $d') => h_) in
      (d', p')
    else 
      Control.throw InteractFailure
  (* Left non-binder rules. *)
  | Side Left :: choices, i :: subh, subc => 
    lazy_match! h with 
    (* Left-and. *)
    | ?hA /\ ?hB =>  
      if Int.equal i 1 then   
        let (d, p) := back hA subh c subc choices in
        let p_type := '($h -> $d -> $c) in
        let p' := '((fun (ab_ : $h) (d_ : $d) => $p (proj1 ab_) d_)) in
        (d, p')
      (*else if Int.equal i 2 then *)
      else Control.throw InteractFailure
    | _ => Control.throw InteractFailure
    end
  (* Left binder, instantiated. *)
  | Binder Left (Some w) :: choices, 1 :: subh, subc => 
    lazy_match! h with 
    | forall x : ?ha, @?hb x => 
      let (d, p) := back '($hb $w) subh c subc choices in 
      let p' := '(fun (xb_ : forall x, $hb x) (d_ : $d) => $p (xb_ $w) d_) in
      (d, p')
    | _ => Control.throw InteractFailure
    end
  (* Left binder, non-instantiated. *)
  | Binder Left None :: choices, 1 :: subh, subc => 
    lazy_match! h with 
    | forall x : ?ha, @?hb x => 
      let ev_x := fresh_evar x (Some ha) in
      let (d, p) := back '($hb $ev_x) subh c subc choices in
      let d := abstract_evar ev_x d in
      let p := abstract_evar ev_x p in
      let d' := '(ex $d) in
      let p' := '(
        fun (xb_ : forall x, $hb x) (ex_xd : $d') => 
          match ex_xd with 
          | ex_intro x0 dx0 => ($p x0) (xb_ x0) dx0
          end    
      ) in
      (d', p')
    | _ => Control.throw InteractFailure
    end
  (* No matching rule. *)
  | _ => Control.throw InteractFailure
  end.

Parameter (A B : Prop).
Parameter (P : nat -> Prop).


Lemma test (h : forall x, P x /\ A) : P 0.
Proof.
  let (new_concl, proof) := 
    back (Constr.type 'h) [ 1 ; 1 ] '(P 0) [] [ Binder Left (Some '0) ; Side Left ] 
  in
  printf "%t" proof; apply ($proof h).


Lemma test (h : A /\ B) : A.
Proof.
  let (new_concl, proof) := back (Constr.type 'h) [ 1 ] 'A [] [ Left ] in
  printf "%t" proof; apply ($proof h).
