From Ltac2 Require Import Ltac2 Printf.


(**********************************************************************************)
(** Utils. *)

(* [beta_equiv t1 t2] checks whether the terms [t1] and [t2] are beta equivalent. *)
Ltac2 beta_equiv (t1 : constr) (t2 : constr) : bool := 
  let t1 := Std.eval_cbv RedFlags.all t1 in 
  let t2 := Std.eval_cbv RedFlags.all t2 in 
  Constr.equal t1 t2.

(* [freh_evar basename type] creates a fresh evar, optionally with the type [type]. 
   The evar is added as a hypothesis, generating a fresh name from the given [basename]. 
   Returns the identifier of the created hypothesis. *)
Ltac2 fresh_evar (id : ident) (type_opt : constr option) : ident := 
  let id := Fresh.in_goal id in  
  match type_opt with 
  | Some type => epose (_ : $type) as $id ; cbv in $id
  | None => epose _ as $id
  end ;
  id.
    
(* [abstract_ident ev c] replaces all occurences of the identifier [id] in [c]
   by a local (de Bruijn) variable, and binds this local variable with a lambda abstraction. 
   
   For instance : 
     [abstract_ident x (P x /\ A)] would give [fun x => P x /\ A]
     [abstract_ident y (P x /\ A)] would give [fun _ => P x /\ A]
*)
Ltac2 abstract_ident (id : ident) (c : constr) : constr :=
  (* First replace [id] by [Rel 0]. *)
  let body := Constr.Unsafe.closenl [ id ] 1 c in
  (* Create the binder. *)
  let type := Constr.type (Constr.Unsafe.make (Constr.Unsafe.Var id)) in 
  let binder := Constr.Binder.make (Some id) type in
  (* Make the lambda abstraction. *)
  Constr.Unsafe.make (Constr.Unsafe.Lambda binder body).

(* [beta_root c] forces the beta reduction at the root of [c], if [c] is a beta redex.
   Otherwise it returns [c] unchanged. *)
Ltac2 beta_root (c : constr) : constr := 
  lazy_match! c with 
  | ?f ?x => 
    match Constr.Unsafe.kind f with 
    | Constr.Unsafe.Lambda _ body => Constr.Unsafe.substnl [ x ] 0 body
    | _ => c
    end
  | _ => c
  end.

(* [fun_to_forall f] returns a term beta-equivalent to [forall x, f x], 
   but when [f] is a lambda abstarction we take care to keep the binder name of [f] 
   and to beta reduce [f x]. *)
Ltac2 fun_to_forall (f : constr) : constr := 
  match Constr.Unsafe.kind f with 
  | Constr.Unsafe.Lambda binder body => 
    Constr.Unsafe.make (Constr.Unsafe.Prod binder body)
  | _ => '(forall x, $f x)
  end.

(* [deep_pattern pat c sub] is the same as [Std.eval_pattern [ (a, Std.AllOccurences) ] c],
   except that we only abstract occurences of [a] which are in the subterm of [c] at path [sub]. *)
Ltac2 deep_pattern (pat : constr) (c : constr) (sub : int list) : constr :=
  (* TODO : actually use [sub]. *)
  Std.eval_pattern [ (pat, Std.AllOccurrences) ] c.

(**********************************************************************************)
(** Interaction. *)

(* When two formulas interact [A |- B] or [A * B],
   [A] is on the [Left] side and [B] is on the [Right] side. *)
Ltac2 Type side := 
  [ Left | Right ].

(* [swap_side s] maps Left to Right and vice-versa. *)
Ltac2 swap_side (s : side) : side := 
  match s with 
  | Left => Right 
  | Right => Left 
  end.

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

(* [swap_choice c] swaps the side of [c]. *)
Ltac2 swap_choice (c : choice) : choice := 
  match c with 
  | Side s => Side (swap_side s)
  | Binder s witness => Binder (swap_side s) witness
  end.

(* A drag and drop kind. *)
Ltac2 Type dnd_kind :=
  [ (* Subformula linking : both sides of the link are
       formulas in the first order skeleton. *)
    Subform
  | (* Deep rewrite where the equality is on the given side. *)
    Rewrite (side)
  ].

(* [swap_dnd_kind kind] swaps the side of [kind] is it is of the form [Rewrite side]. *)
Ltac2 swap_dnd_kind (kind : dnd_kind) : dnd_kind :=
  match kind with 
  | Subform => Subform 
  | Rewrite side => Rewrite (swap_side side)
  end.

(* An exception raised when back/forward fails. 
   The string is a short message explaining the reason for the failure. *)
Ltac2 Type exn ::= [ InteractFailure (string) ].

(* [apply_choices choices x] applies each witness in [choices] to the argument [x], 
   and leaves sides unchanged. *)
Ltac2 apply_choices (choices : choice list) (x : constr) : choice list :=
  List.map 
    (fun c => 
      match c with 
      | Side side => Side side  
      | Binder side None => Binder side None 
      | Binder side (Some witness) => Binder side (Some '($witness $x))
      end)
    choices. 

Check eq_ind_r.

(* [back h subh c subc choices kind] should produce a result (d, p) such that : 
   - d is the new conclusion. 
   - p is a proof of h -> d -> c. 

   In case of a deep rewrite, the path should point to the argument of the equality
   which is substituted.
*)
Ltac2 rec back 
  (h : constr) 
  (subh : int list) 
  (c : constr) 
  (subc : int list) 
  (choices : choice list) 
  (kind : dnd_kind)
  : constr * constr 
:= 
  (* Put the two terms in head normal form. *)
  let h := eval hnf in $h in 
  let c := eval hnf in $c in 
  (* Print the link. *)
  printf "Backward : %t |- %t" h c;
  match choices, subh, subc, kind with
  (****************************************************************************)
  (* End rules *)
  (****************************************************************************)
  (* id. *)
  | [], [], [], Subform => 
    if beta_equiv h c then 
      let d' := 'True in 
      let p' := '(fun (h_ : $h) (_ : $d') => (h_ : $c)) in
      (d', p')
    else 
      Control.throw (InteractFailure "[back] id rule : terms are not beta convertible")
  (* L=1. *)
  | [], [ 2 ], subc, Rewrite Left => 
    lazy_match! h with 
    | @eq ?ty ?a ?b => 
      (* Rewrite a into b. *)
      lazy_match! deep_pattern a c subc with
      | ?f _ => 
        let d' := beta_root '($f $b) in
        let p' := '(fun (h_ : $h) (d_ : $d') => @eq_ind_r $ty $b $f d_ $a h_) in
        (d', p')
      | _ => Control.throw (InteractFailure "[back] L=1 rule : bad result from deep_pattern") 
      end
    | _ => Control.throw (InteractFailure "[back] L=1 rule : expected an equality")
    end
  (* L=2. *)
  | [], [ 3 ], subc, Rewrite Left => 
    lazy_match! h with 
    | @eq ?ty ?a ?b => 
      (* Rewrite b into a. *)
      lazy_match! deep_pattern b c subc with
      | ?f _ => 
        let d' := beta_root '($f $a) in
        let p' := '(fun (h_ : $h) (d_ : $d') => @eq_ind $ty $a $f d_ $b h_) in
        (d', p')
      | _ => Control.throw (InteractFailure "[back] L=2 rule : bad result from deep_pattern") 
      end
    | _ => Control.throw (InteractFailure "[back] L=2 rule : expected an equality")
    end
  (****************************************************************************)
  (* Left non-binder rules. *)
  (****************************************************************************)
  | Side Left :: choices, i :: subh, subc, _ => 
    lazy_match! h with 
    (* L∧. *)
    | ?hA /\ ?hB =>  
      (* L∧1. *)
      if Int.equal i 1 then   
        let (d, p) := back hA subh c subc choices kind in
        let p' := '(fun (ab_ : $h) (d_ : $d) => $p (proj1 ab_) d_) in
        (d, p')
      (* L∧2. *)
      else if Int.equal i 2 then 
        let (d, p) := back hB subh c subc choices kind in 
        let p' := '(fun (ab_ : $h) (d_ : $d) => $p (proj2 ab_) d_) in
        (d, p') 
      else Control.throw (InteractFailure "[back] L∧ rule : invalid index")
    (* L∨. *)
    | ?hA \/ ?hB => 
      (* L∨1. *)
      if Int.equal i 1 then 
        let (d, p) := back hA subh c subc choices kind in 
        let d' := '($d /\ ($hB -> $c)) in 
        let p' := 
          '(fun (ab_ : $h) (d_ : $d') => 
              match ab_ with 
              | @or_introl _ _ a_ => $p a_ (proj1 d_)
              | @or_intror _ _ b_ => (proj2 d_) b_
              end) 
        in (d', p')
      (* L∨2. *)
      else if Int.equal i 2 then 
        let (d, p) := back hB subh c subc choices kind in 
        let d' := '(($hA -> $c) /\ $d) in
        let p' := 
          '(fun (ab_ : $h) (d_ : $d') => 
              match ab_ with 
              | @or_introl _ _ a_ => (proj1 d_) a_
              | @or_intror _ _ b_ => $p b_ (proj2 d_)
              end)
        in (d', p')
      else Control.throw (InteractFailure "[back] L∨ rule : invalid index")
    (* L⇒2. *)
    | ?hA -> ?hB => 
      if Int.equal i 1 then 
        let (d, p) := back hB subh c subc choices kind in 
        let d' := '($hA /\ $d) in
        let p' := '(fun (h_ : $h) (d_ : $d') => $p (h_ (proj1 d_)) (proj2 d_)) in
        (d', p')
      else Control.throw (InteractFailure "[back] L⇒ rule : invalid index") 
    | _ => Control.throw (InteractFailure "[back] unexpected head constructor")
    end
  (****************************************************************************)
  (* Right non-binder rules. *)
  (****************************************************************************)
  | Side Right :: choices, subh, i :: subc, _ =>
    lazy_match! c with 
    (* R∧. *)
    | ?cA /\ ?cB => 
      (* R∧1. *)
      if Int.equal i 1 then 
        let (d, p) := back h subh cA subc choices kind in 
        let d' := '($d /\ $cB) in
        let p' := '(fun (h_ : $h) (d_ : $d') => conj ($p h_ (proj1 d_)) (proj2 d_)) in
        (d', p')
      (* R∧2. *)
      else if Int.equal i 2 then 
        let (d, p) := back h subh cB subc choices kind in 
        let d' := '($cA /\ $d) in
        let p' := '(fun (h_ : $h) (d_ : $d') => conj (proj1 d_) ($p h_ (proj2 d_))) in
        (d', p')
      else Control.throw (InteractFailure "[back] rule R∧ : invalid index")
    (* R∨. *)
    | ?cA \/ ?cB => 
      (* R∨1. *)
      if Int.equal i 1 then 
        let (d, p) := back h subh cA subc choices kind in 
        let d' := '($d \/ $cB) in
        let p' := 
          '(fun (h_ : $h) (d_ : $d') => 
              match d_ with 
              | @or_introl _ _ d_ => @or_introl $cA $cB ($p h_ d_)
              | @or_intror _ _ b_ => @or_intror $cA $cB b_
            end)
        in (d', p')
      (* R∨2. *)
      else if Int.equal i 2 then 
        let (d, p) := back h subh cB subc choices kind in 
        let d' := '($cA \/ $d) in
        let p' := 
          '(fun (h_ : $h) (d_ : $d') => 
              match d_ with 
              | @or_introl _ _ a_ => @or_introl $cA $cB a_
              | @or_intror _ _ d_ => @or_intror $cA $cB ($p h_ d_)
            end)
        in (d', p')
      else Control.throw (InteractFailure "[back] rule R∨ : invalid index")
    (* R⇒. *)
    | ?cA -> ?cB => 
      (* R⇒1. *)
      if Int.equal i 0 then 
        let (d, p) := forward h subh cA subc choices kind in 
        let d' := '($d -> $cB) in
        (* p : h -> cA -> d *) 
        let p' := '(fun (h_ : $h) (d_ : $d') (cA_ : $cA) => d_ ($p h_ cA_)) in 
        (d', p')
      (* R⇒2. *)
      else if Int.equal i 1 then 
        let (d, p) := back h subh cB subc choices kind in 
        let d' := '($cA -> $d) in
        let p' := '(fun (h_ : $h) (d_ : $d') (cA_ : $cA) => $p h_ (d_ cA_)) in 
        (d', p')
      else Control.throw (InteractFailure "[back] rule R⇒ : invalid index")
    | _ => Control.throw (InteractFailure "[back] unexpected head constructor")
    end 
  (****************************************************************************)
  (* Left binder, instantiated. *)
  (****************************************************************************)
  | Binder Left (Some w) :: choices, 1 :: subh, subc, _ => 
    lazy_match! h with 
    (* L∀i. *)
    | forall x : ?ha, @?hb x => 
      let (d, p) := back '($hb $w) subh c subc choices kind in 
      let p' := '(fun (xb_ : forall x, $hb x) (d_ : $d) => $p (xb_ $w) d_) in
      (d, p')
    | _ => Control.throw (InteractFailure "[back] unexpected head constructor")
    end
  (****************************************************************************)
  (* Right binder, instantiated. *)
  (****************************************************************************)
  | Binder Right (Some w) :: choices, subh, 1 :: subc, _ => 
    lazy_match! c with 
    (* R∃i. *)
    | exists x : ?ca, @?cb x => 
      let (d, p) := back h subh '($cb $w) subc choices kind in 
      let p' := '(fun (h_ : $h) (d_ : $d) => @ex_intro $ca $cb $w ($p h_ d_)) in
      (d, p')
    | _ => Control.throw (InteractFailure "[back] unexpected head constructor")
    end
  (****************************************************************************)
  (* Left binder, non-instantiated. *)
  (****************************************************************************)
  | Binder Left None :: choices, 1 :: subh, subc, _ =>
    lazy_match! h with 
    (* L∀s. *)
    | forall x : ?ha, @?hb x => 
      let ev := fresh_evar @ev (Some ha) in
      let ev_constr := Constr.Unsafe.make (Constr.Unsafe.Var ev) in
      let (d, p) := back '($hb $ev_constr) subh c subc (apply_choices choices ev_constr) kind in
      let d := abstract_ident ev d in
      let p := abstract_ident ev p in
      let d' := '(ex $d) in
      let p' := 
        '(fun (xb_ : forall x, $hb x) (ex_xd : $d') => 
            match ex_xd with 
            | ex_intro _ x0 dx0 => ($p x0) (xb_ x0) dx0
            end) 
      in
      (* Don't forget to clear the evar. *)
      clear ev ; (d', p')
    (* L∃s. *)
    | exists x : ?ha, @?hb x => 
      let ev := fresh_evar @ev (Some ha) in
      let ev_constr := Constr.Unsafe.make (Constr.Unsafe.Var ev) in
      let (d, p) := back '($hb $ev_constr) subh c subc (apply_choices choices ev_constr) kind in
      let d := abstract_ident ev d in
      let p := abstract_ident ev p in
      let d' := fun_to_forall d in
      let p' := 
        '(fun (xb_ : exists x, $hb x) (xd_ : $d') => 
            match xb_ with 
            | ex_intro _ x0 bx0 => ($p x0) bx0 (xd_ x0)
            end) 
      in
      (* Don't forget to clear the evar. *)
      clear ev ; (d', p')
    | _ => Control.throw (InteractFailure "[back] unexpected head constructor")
    end
  (****************************************************************************)
  (* Right binder, non-instantiated. *)
  (****************************************************************************)
  | Binder Right None :: choices, subh, 1 :: subc, _ =>
    lazy_match! c with 
    (* R∀s. *)
    | forall x : ?ca, @?cb x => 
      let ev := fresh_evar @ev (Some ca) in
      let ev_constr := Constr.Unsafe.make (Constr.Unsafe.Var ev) in
      let (d, p) := back h subh '($cb $ev_constr) subc (apply_choices choices ev_constr) kind in
      let d := abstract_ident ev d in
      let p := abstract_ident ev p in
      let d' := fun_to_forall d in
      let p' := '(fun (h_ : $h) (xd_ : $d') (x : $ca) => ($p x) h_ (xd_ x)) in
      (* Don't forget to clear the evar. *)
      clear ev ; (d', p')
    (* R∃s. *)
    | exists x : ?ca, @?cb x => 
      let ev := fresh_evar @ev (Some ca) in
      let ev_constr := Constr.Unsafe.make (Constr.Unsafe.Var ev) in
      let (d, p) := back h subh '($cb $ev_constr) subc (apply_choices choices ev_constr) kind in
      let d := abstract_ident ev d in
      let p := abstract_ident ev p in
      let d' := '(ex $d) in
      (* p x : h -> d x -> cb x *)
      let p' := 
        '(fun (h_ : $h) (xd_ : $d') => 
            match xd_ with 
            | ex_intro _ x0 dx0 => ex_intro $cb x0 (($p x0) h_ dx0)
            end)
      in
      (* Don't forget to clear the evar. *)
      clear ev ; (d', p')  
    | _ => Control.throw (InteractFailure "[back] unexpected head constructor")
    end
  (****************************************************************************)
  (* No matching rule. *)
  (****************************************************************************)
  | _ => Control.throw (InteractFailure "[back] unexpected head constructor")
  end
  
(* [forward h1 sub1 h2 sub2 choices kind swapped] should produce a result (d, p) such that : 
   - d is the new hypothesis. 
   - p is a proof of h1 -> h2 -> d. 

   Arguments : 
   - h1 is the (type of the) first hypothesis. 
   - sub1 is the path in h1. 
   - h2 is the (type of the) second hypothesis. 
   - sub2 is the path in h2.
   - choices is the list of choices (left/right + instantiation witnesses).
   - kind is the drag and drop kind.
*)
with forward 
  (h1 : constr) 
  (sub1 : int list) 
  (h2 : constr) 
  (sub2 : int list) 
  (choices : choice list) 
  (kind : dnd_kind)
  : constr * constr 
:= 
  (* Put the two terms in head normal form. *)
  let h1 := eval hnf in $h1 in 
  let h2 := eval hnf in $h2 in 
  (* Print the link. *)
  printf "Forward : %t * %t" h1 h2;
  match choices, sub1, sub2, kind with
  (****************************************************************************)
  (* End rules. *)
  (****************************************************************************)
  (* F=1. *)
  | [], [ 2 ], sub2, Rewrite Left => 
    lazy_match! h1 with 
    | @eq ?ty ?a ?b => 
      (* Rewrite a into b. *)
      lazy_match! deep_pattern a h2 sub2 with
      | ?f _ => 
        let d' := beta_root '($f $b) in
        let p' := '(fun (h1_ : $h1) (h2_ : $h2) => @eq_ind $ty $a $f h2_ $b h1_) in
        (d', p')
      | _ => Control.throw (InteractFailure "[forward] F=1 rule : bad result from deep_pattern") 
      end
    | _ => Control.throw (InteractFailure "[forward] F=1 rule : expected an equality")
    end
  (* F=2. *)
  | [], [ 3 ], sub2, Rewrite Left =>
    lazy_match! h1 with 
    | @eq ?ty ?a ?b => 
      (* Rewrite b into a. *)
      lazy_match! deep_pattern b h2 sub2 with
      | ?f _ => 
        let d' := beta_root '($f $a) in
        let p' := '(fun (h1_ : $h1) (h2_ : $h2) => @eq_ind_r $ty $b $f h2_ $a h1_) in
        (d', p')
      | _ => Control.throw (InteractFailure "[forward] L=2 rule : bad result from deep_pattern") 
      end
    | _ => Control.throw (InteractFailure "[forward] L=2 rule : expected an equality")
    end
  (****************************************************************************)
  (* Swap sides. *)
  (****************************************************************************)
  | Side Right :: _, _, _, _ =>
    forward h2 sub2 h1 sub1 (List.map swap_choice choices) (swap_dnd_kind kind)
  | (Binder Right _) :: _, _, _, _ =>
    forward h2 sub2 h1 sub1 (List.map swap_choice choices) (swap_dnd_kind kind)
  (****************************************************************************)
  (* No matching rule. *)
  (****************************************************************************)
  | _ => Control.throw (InteractFailure "[forward] unexpected head constructor")
  end.

Ltac2 back_hyp_goal (h : ident) (subh : int list) (subc : int list) (choices : choice list) (kind : dnd_kind) : unit := 
  let hyp := Control.hyp h in  
  let concl := Control.goal () in 
  let (new_concl, proof) := back (Constr.type hyp) subh concl subc choices kind in
  printf "%t" proof ; 
  refine '($proof $hyp _).

(******************************************************************************)
(** Debugging area. *)

Parameter (A B : Prop).
Parameter (P : nat -> Prop).

Lemma test' x (h : 3 = x) : P x -> A.
Proof.  
  back_hyp_goal @h [ 3 ] [ 0 ] [ Side Right ] (Rewrite Left). 
Admitted. 

Lemma test (h : A) : A -> B.
Proof.
(*  back_hyp_goal @h [ ] [ 0 ] [ Side Right ] Subform.*)
Admitted.
