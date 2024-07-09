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

(**********************************************************************************)
(** Interaction. *)

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

(* A drag and drop kind. *)
Ltac2 Type dnd_kind :=
  [ (* Subformula linking : both sides of the link are
       formulas in the first order skeleton. *)
    Subform
  | (* Deep rewrite : the *left* side of the link is an equality
       which rewrites in the right side. *)
    RewriteL
  | (* Deep rewrite : the *right* side of the link is an equality
       which rewrites in the left side. *)
    RewriteR
  ].

Ltac2 Type exn ::= [ InteractFailure ].

Check eq_ind.

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
      Control.throw InteractFailure
  (* L=1. *)
  | [ Side Left ], [], [], RewriteL => 
    lazy_match! h with 
    | @eq ?ty ?a ?b => 
      (* Rewrite a into b. *)
      lazy_match! Std.eval_pattern [ (a, Std.AllOccurrences) ] c with
      | ?f _ => 
        let d' := beta_root '($f $b) in
        let p' := '(fun (h_ : $h) (d_ : $d') => @eq_ind_r $ty $b $f d_ $a h_) in
        (d', p')
      | _ => Control.throw InteractFailure 
      end
    | _ => Control.throw InteractFailure
    end
  (* L=2. *)
  | [ Side Right ], [], [], RewriteL => 
    lazy_match! h with 
    | @eq ?ty ?a ?b => 
      (* Rewrite b into a. *)
      lazy_match! Std.eval_pattern [ (b, Std.AllOccurrences) ] c with
      | ?f _ => 
        let d' := beta_root '($f $a) in
        let p' := '(fun (h_ : $h) (d_ : $d') => @eq_ind $ty $a $f d_ $b h_) in
        (d', p')
      | _ => Control.throw InteractFailure 
      end
    | _ => Control.throw InteractFailure
    end
  (****************************************************************************)
  (* Left non-binder rules. *)
  (****************************************************************************)
  | Side Left :: choices, i :: subh, subc, _ => 
    lazy_match! h with 
    (* L∧i. *)
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
      else Control.throw InteractFailure
    (* L∨i. *)
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
      else Control.throw InteractFailure
    | _ => Control.throw InteractFailure
    end
  (****************************************************************************)
  (* Right non-binder rules. *)
  (****************************************************************************)
  | Side Right :: choices, subh, i :: subc, _ =>
    lazy_match! c with 
    (* R∧i. *)
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
      else Control.throw InteractFailure
    (* R∨i. *)
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
      else Control.throw InteractFailure
    | _ => Control.throw InteractFailure
    end 
  (****************************************************************************)
  (* Left binder, instantiated. *)
  (****************************************************************************)
  | Binder Left (Some w) :: choices, 1 :: subh, subc, _ => 
    lazy_match! h with 
    | forall x : ?ha, @?hb x => 
      let (d, p) := back '($hb $w) subh c subc choices kind in 
      let p' := '(fun (xb_ : forall x, $hb x) (d_ : $d) => $p (xb_ $w) d_) in
      (d, p')
    | _ => Control.throw InteractFailure
    end
  (****************************************************************************)
  (* Left binder, non-instantiated. *)
  (****************************************************************************)
  | Binder Left None :: choices, 1 :: subh, subc, _ =>
    lazy_match! h with 
    | forall x : ?ha, @?hb x => 
      let ev := fresh_evar @ev (Some ha) in
      let ev_constr := Constr.Unsafe.make (Constr.Unsafe.Var ev) in
      let (d, p) := back '($hb $ev_constr) subh c subc choices kind in
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
    | _ => Control.throw InteractFailure
    end
  (****************************************************************************)
  (* No matching rule. *)
  (****************************************************************************)
  | _ => Control.throw InteractFailure
  end.

Ltac2 back_hyp_goal (h : ident) (subh : int list) (subc : int list) (choices : choice list) (kind : dnd_kind) : unit := 
  let hyp := Control.hyp h in  
  let concl := Control.goal () in 
  let (new_concl, proof) := back (Constr.type hyp) subh concl subc choices kind in
  printf "%t" proof ; 
  refine '($proof $hyp _).

Parameter (A B : Prop).
Parameter (P : nat -> Prop).

Lemma test x (h : 2 = x) : P x \/ A.
Proof.
  back_hyp_goal @h [ ] [ 1 ] [ Side Right ; Side Right ] RewriteL.
Admitted.


Lemma test' (h : forall x, P x \/ P 0) : P 0.
Proof.  
  back_hyp_goal @h [ 1 ; 2 ] [] [ Binder Left None ; Side Left ]. 
  

