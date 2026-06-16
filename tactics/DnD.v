(* This module defines the tactics that perform deep interaction
   (i.e. drag and drop). The main tactics are the mutually recursive 
   functions [back] and [forward]. These tactics are called from 
   Ocaml, see plugin/actions.ml. *)

From Ltac2 Require Import Ltac2 Printf.
From Actema Require Import Utils. 



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


Require Import Ltac2.Ltac2.

(* Vérifie si un terme est un beta-redex avec le nom donné *)
Ltac2 est_beta_redex_avec_nom (t : constr) (nom : ident) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      if Int.equal (Array.length args) 1 then
        match Constr.Unsafe.kind f with
        | Constr.Unsafe.Lambda binder _ =>
            match Constr.Binder.name binder with
            | Some id => Ident.equal id nom
            | None => false
            end
        | _ => false
        end
      else
        false
  | _ => false
  end.

(* Parcourt récursivement le terme et réduit les beta-redexes sélectifs *)
Ltac2 rec reduce_beta_selective_aux (nom : ident) (t : constr) : constr :=
  (* D'abord vérifier si c'est un beta-redex à réduire *)
  if est_beta_redex_avec_nom t nom then
    (* Réduire ce redex *)
    let t_reduit := Std.eval_cbv RedFlags.beta t in
    (* Continuer à parcourir le résultat *)
    reduce_beta_selective_aux nom t_reduit
  else
    (* Parcourir la structure du terme *)
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f args =>
        let f' := reduce_beta_selective_aux nom f in
        let args' := Array.map (reduce_beta_selective_aux nom) args in
        Constr.Unsafe.make (Constr.Unsafe.App f' args')
    
    | Constr.Unsafe.Lambda binder body =>
        let body' := reduce_beta_selective_aux nom body in
        let binder' := Constr.Binder.unsafe_make 
                        (Constr.Binder.name binder)
                        (Constr.Binder.relevance binder)
                        (reduce_beta_selective_aux nom (Constr.Binder.type binder))
                        in
        Constr.Unsafe.make (Constr.Unsafe.Lambda binder' body')
    
    | Constr.Unsafe.Prod binder body =>
        let body' := reduce_beta_selective_aux nom body in
        let binder' := Constr.Binder.unsafe_make 
                        (Constr.Binder.name binder)
                        (Constr.Binder.relevance binder)
                        (reduce_beta_selective_aux nom (Constr.Binder.type binder)) in
        Constr.Unsafe.make (Constr.Unsafe.Prod binder' body')
    
    | Constr.Unsafe.LetIn binder val_def body =>
        let val_def' := reduce_beta_selective_aux nom val_def in
        let body' := reduce_beta_selective_aux nom body in
        let binder' := Constr.Binder.unsafe_make 
                        (Constr.Binder.name binder)
                        (Constr.Binder.relevance binder)
                        (reduce_beta_selective_aux nom (Constr.Binder.type binder)) in
        Constr.Unsafe.make (Constr.Unsafe.LetIn binder' val_def' body')

  | Constr.Unsafe.Case case_info (case_ret, r) case_invert discriminant branches =>
        let case_ret' := reduce_beta_selective_aux nom case_ret in
        let discriminant' := reduce_beta_selective_aux nom discriminant in
        let branches' := Array.map (reduce_beta_selective_aux nom) branches in
        Constr.Unsafe.make (Constr.Unsafe.Case case_info (case_ret', r)
                                               case_invert discriminant' branches')
   
                           
     (* Pour les autres cas, retourner le terme inchangé *)
    | _ => t
    end.

(* Tactique principale : réduit les beta-redexes avec le nom donné dans le goal *)

Ltac2 toto () := Ident.of_string "my_dnd_ident".
Ltac2 my_bind() := Option.get(toto()).



Ltac2 reduce_beta_selective () : unit :=
  let goal := Control.goal () in
  let goal_reduit := reduce_beta_selective_aux (my_bind()) goal in
 change $goal_reduit.


     (* Exemple d'utilisation : 
   Goal forall n, (fun `(toto()) => (toto()) + 1) n + (fun y => y * 2) n = n + 1 + n * 2.
   Proof.
     intro.
     reduce_beta_selective ().
     (* Réduit seulement (fun x => x + 1) n, pas (fun y => y * 2) n *)
   Qed.
*)


Ltac2 select_beta t :=  reduce_beta_selective_aux (my_bind()) t.

(* A choice of rule to apply. *)
Ltac2 Type choice := 
  [ (* Swap the sides of the link. *)
    Swap
  | (* Apply the next non-binder rule on the given side. *)
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
  | Swap => Swap
  | Side s => Side (swap_side s)
  | Binder s witness => Binder (swap_side s) witness
  end.

Ltac2 swap_choices (ch : choice list) : choice list :=
   List.map swap_choice ch.

(* A drag and drop kind. This is used to know which end rule to apply :
   without this information there could be ambiguities. *)
Ltac2 Type dnd_kind :=
  [ (* Subformula linking : both sides of the link are
       formulas in the first order skeleton. *)
    Subform
  | (* Deep rewrite where the equality is in the formula on the given side. *)
    Rewrite (side)
  ].

(* [swap_dnd_kind kind] swaps the side of [kind] if it is of the form [Rewrite side]. *)
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
      | Swap => Swap
      | Side side => Side side  
      | Binder side None => Binder side None 
      | Binder side (Some witness) => Binder side (Some '($witness $x))
      end)
    choices. 

(* [back h subh c subc choices kind] should produce a result (d, p) such that : 
   - d is the new conclusion. 
   - p is a proof of h -> d -> c. 

   In case of a deep rewrite, the path should point to the argument of the equality
   which is substituted.
 *)

(*
Ltac2 rec path_simpl 
      (t: constr) 
      (l : int list) :=
       match l with
       | [] =>
	     let t' := eval simpl in $t in t'
       |  0::l' =>
	     match t with
            | (f a) =>
		   let f' := (path_simpl f l')
		   in f' 
            | f => let xx := 'True in xx
	end
       | _ => 'True
     end.
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
  let h :=  (beta_root h) in
  let c :=  (beta_root c) in
  (* Print the link. *)
  printf "[back] %t |- %t" h c;
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
         let f := deep_pattern a c subc in
        let d' := beta_root '($f $b) in
        let p' := '(fun (h_ : $h) (d_ : $d') => @eq_ind_r $ty $b $f d_ $a h_) in
      (d', p')
    | _ => Control.throw (InteractFailure "[back] L=1 rule : expected an equality")
    end
  (* L=2. *)
  | [], [ 3 ], subc, Rewrite Left => 
    lazy_match! h with 
    | @eq ?ty ?a ?b => 
        (* Rewrite b into a. *)
        let f := deep_pattern b c subc in
        let d' := beta_root '($f $a) in
        let p' := '(fun (h_ : $h) (d_ : $d') => @eq_ind $ty $a $f d_ $b h_) in
        (d', p')
    | _ => Control.throw (InteractFailure "[back] L=2 rule : expected an equality")
    end
  (****************************************************************************)
  (* Left non-binder rules. *)
  (****************************************************************************)
  | Side Left :: choices, i :: subh, subc, _ => 
    lazy_match! h with 
  (* L⇔ *)
    | ?hA <-> ?hB => 
      if Int.equal i 1 then
	let (d,p) := back hA subh c subc choices kind in
	let d' := '($hB /\ $d) in
        let p' := '(fun (ab_ : $h) (d_ : $d') => $p (proj2 ab_ (proj1 d_)) (proj2 d_)) in
        (d', p')
      else if Int.equal i 2 then
	let (d,p) := back hB subh c subc choices kind in
	let d' := '($hA /\ $d) in
        let p' := '(fun (ab_ : $h) (d_ : $d') => $p (proj1 ab_ (proj1 d_)) (proj2 d_)) in
        (d', p')
	   else Control.throw (InteractFailure "[back] L⇔ rule : invalid index") 
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
    | _ => Control.throw (InteractFailure 
      "[back] unexpected head constructor for [Side Left]")
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
    (* Rnot *)
    | (not ?cA) =>
        if Int.equal i 0 then 
          let (d, p) := forward h subh cA subc choices kind in 
        let d' := '(not $d) in
        (* p : h -> cA -> d *) 
        let p' := '(fun (h_ : $h) (d_ : $d') (cA_ : $cA) => d_ ($p h_ cA_)) in 
        (d', p')
        else Control.throw (InteractFailure "[back] rule Rnot : invalid index") 
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

    | _ => Control.throw (InteractFailure 
      "[back] unexpected head constructor for [Side Right]")
    end 
  (****************************************************************************)
  (* Left binder, instantiated. *)
  (****************************************************************************)
  | Binder Left (Some w) :: choices, 1 :: subh, subc, _ => 
    lazy_match! h with 
    (* L∀i. *)
    | forall x : ?ha, @?hb x =>
        let w' := beta_root w in
        let hb' := beta_root '($hb $w') in
        let (d, p) := back hb' subh c subc choices kind in
        (* let xd_ := my_bind() in *)
      let p' := '(fun (h_ : forall x, $hb x) (d_ : $d) => $p (h_ $w) d_) in
      (d, p')
    | _ => Control.throw (InteractFailure 
      "[back] unexpected head constructor for [Binder Left (Some _)]")
    end
  (****************************************************************************)
  (* Right binder, instantiated. *)
  (****************************************************************************)
  | Binder Right (Some w) :: choices, subh, 1 :: subc, _ => 
    lazy_match! c with 
    (* R∃i. *)
    | exists x : ?ca, @?cb x =>
        let cb' := beta_root '($cb $w) in
      let (d, p) := back h subh cb' subc choices kind in 
      let p' := '(fun (h_ : $h) (d_ : $d) => @ex_intro $ca $cb $w ($p h_ d_)) in
      let p'' := (beta_root p') in
      (d, p'')
    | _ => Control.throw (InteractFailure 
      "[back] unexpected head constructor for [Binder Right (Some _)]")
    end
  (****************************************************************************)
  (* Left binder, non-instantiated. *)
  (****************************************************************************)
  | Binder Left None :: choices, 1 :: subh, subc, _ =>
    lazy_match! h with 
    (* L∀s. *)
    | forall x : ?ha, @?hb x => 
      let x := Option.default @x (binder_name hb) in
      let ev := fresh_evar (Some x) (Some ha) in
      let ev_constr := mk_var ev in
      let (d, p) := back '($hb $ev_constr) subh c subc (apply_choices choices ev_constr) kind in
      let d := abstract_ident ev d in
      let p := abstract_ident ev p in
      let d' := '(ex $d) in
      let p' := 
        '(fun (my_dnd_ident : forall x, $hb x) (ex_xd : $d') => 
            match ex_xd with 
            | ex_intro _ x0 dx0 => ($p x0) (my_dnd_ident x0) dx0
            end) 
      in
      (* Don't forget to clear the evar. *)
      Std.clear [ ev ] ; (d', p')
    (* L∃s. *)
    | exists x : ?ha, @?hb x => 
      let x := Option.default @x (binder_name hb) in 
      let ev := fresh_evar (Some x) (Some ha) in
      let ev_constr := mk_var ev in
      let hb' := beta_root '($hb $ev_constr) in
      let (d, p) := back hb' subh c subc (apply_choices choices ev_constr) kind in
      let d := abstract_ident ev d in
      let p := abstract_ident ev p in
      let d' := fun_to_forall (Some x) d in
      let p' := 
        '(fun (xb_ : exists x, $hb x) (my_dnd_ident : $d') => 
            match xb_ with 
            | ex_intro _ x0 bx0 => ($p x0) bx0 (my_dnd_ident x0)
            end) 
      in
      (* Don't forget to clear the evar. *)
      Std.clear [ ev ] ; (d', p')
    | _ => Control.throw (InteractFailure 
      "[back] unexpected head constructor for [Binder Left None]")
    end
  (****************************************************************************)
  (* Right binder, non-instantiated. *)
  (****************************************************************************)
  | Binder Right None :: choices, subh, 1 :: subc, _ =>
    lazy_match! c with 
    (* R∀s. *)
    | forall x : ?ca, @?cb x => 
      let x := Option.default @x (binder_name cb) in 
      let ev := fresh_evar (Some x) (Some ca) in
      let ev_constr := mk_var ev in
      let (d, p) := back h subh '($cb $ev_constr) subc (apply_choices choices ev_constr) kind in
      let d := abstract_ident ev d in
      let p := abstract_ident ev p in
      let d' := fun_to_forall (Some x) d in
 (*     let xd_ := my_bind() in *)
      let p' := '(fun (h_ : $h) (my_dnd_ident : $d') (x : $ca) => ($p x) h_ (my_dnd_ident x)) in
      (* Don't forget to clear the evar. *)
      Std.clear [ ev ] ; (d', p')
    (* R∃s. *)
    | exists x : ?ca, @?cb x => 
      let x := Option.default @x (binder_name cb) in 
      let ev := fresh_evar (Some x) (Some ca) in
      let ev_constr := mk_var ev in
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
      Std.clear [ ev ] ; (d', p')  
    | _ => Control.throw (InteractFailure 
      "[back] unexpected head constructor for [Binder Right None]")
    end
  (****************************************************************************)
  (* No matching rule. *)
  (****************************************************************************)
  | _ => Control.throw (InteractFailure "[back] no matching rule")
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
  let h1 := beta_root h1 in
  let h2 := beta_root h2 in 
  (* Print the link. *)
  printf "[forward] %t * %t" h1 h2; 
  match choices, sub1, sub2, kind with
  (****************************************************************************)
  (* End rules. *)
  (****************************************************************************)
  (* F=1. *)
  | [], sub1, [ 2 ], Rewrite Right => 
    lazy_match! h2 with 
    | @eq ?ty ?a ?b => 
      (* Rewrite a into b. *)
      let f := deep_pattern a h1 sub1 in
      let d' := beta_root '($f $b) in
      let p' := '(fun (h1_ : $h1) (h2_ : $h2) => @eq_ind $ty $a $f h1_ $b h2_) in
      (d', p')
    | _ => Control.throw (InteractFailure "[forward] F=1 rule : expected an equality")
    end
  | [], [2], sub2, Rewrite Left => 
    lazy_match! h1 with 
    | @eq ?ty ?a ?b => 
      (* Rewrite a into b. *)
      let f := deep_pattern a h2 sub2 in
      let d' := beta_root '($f $b) in
      let p' := '(fun (h1_ : $h1) (h2_ : $h2) => @eq_ind $ty $a $f h2_ $b h1_) in
      (d', p')
    | _ => Control.throw (InteractFailure "[forward] F=1 rule : expected an equality")
    end 
  (* F=2. *)
  | [], sub1, [ 3 ], Rewrite Right =>
    lazy_match! h2 with 
    | @eq ?ty ?a ?b => 
      (* Rewrite b into a. *)
      let f := deep_pattern b h1 sub1 in
      let d' := beta_root '($f $a) in
      let p' := '(fun (h1_ : $h1) (h2_ : $h2) => @eq_ind_r $ty $b $f h1_ $a h2_) in
      (d', p')
    | _ => Control.throw (InteractFailure "[forward] F=2 rule : expected an equality")
      end
  | [], [ 3 ], sub2, Rewrite Left =>
    lazy_match! h1 with 
    | @eq ?ty ?a ?b => 
      (* Rewrite b into a. *)
      let f := deep_pattern b h2 sub2 in
      let d' := beta_root '($f $a) in
      let p' := '(fun (h1_ : $h1) (h2_ : $h2) => @eq_ind_r $ty $b $f h2_ $a h1_) in
      (d', p')
    | _ => Control.throw (InteractFailure "[forward] F=2 rule : expected an equality")
      end

  (****************************************************************************)
  (* Non-binder rules. *)
  (****************************************************************************)
  | Side Right :: choices, sub1, i :: sub2, _ => 
    lazy_match! h2 with 
  (* F⇔ *)
    | ?ha <-> ?hb => 
      if Int.equal i 1 then
	let (d,p) := back h1 sub1 ha sub2 choices kind in
	let d' := '($d -> $hb) in
        let p' := '(fun (h1_ : $h1) (h2_ : $h2) (d_ : $d) => (proj1 h2_) ($p h1_ d_)) in
        (d', p')
      else if Int.equal i 2 then
	let (d,p) := back h1 sub1 hb sub2 choices kind in
	let d' := '($d -> $ha) in
        let p' := '(fun (h1_ : $h1) (h2_ : $h2) (d_ : $d) => (proj2 h2_) ($p h1_ d_)) in
        (d', p')
     else 
        Control.throw (InteractFailure "[forward] F⇔ rule : invalid index") 
    (* F∧. *)
    | ?ha /\ ?hb =>  
      (* F∧1. *)
      if Int.equal i 1 then   
        let (d, p) := forward h1 sub1 ha sub2 choices kind in
        let p' := '(fun (h1_ : $h1) (h2_ : $h2) => $p h1_ (proj1 h2_)) in
        (d, p')
      (* F∧2. *)
      else if Int.equal i 2 then 
        let (d, p) := forward h1 sub1 hb sub2 choices kind in 
        let p' := '(fun (h1_ : $h1) (h2_ : $h2) => $p h1_ (proj2 h2_)) in
        (d, p')
      else Control.throw (InteractFailure "[forward] F∧ rule : invalid index")
    (* F∨. *)
    | ?ha \/ ?hb => 
      (* F∨1. *)
      if Int.equal i 1 then 
        let (d, p) := forward h1 sub1 ha sub2 choices kind in 
        let d' := '($d \/ $hb) in 
        let p' := 
          '(fun (h1_ : $h1) (h2_ : $h2) => 
              match h2_ with 
              | @or_introl _ _ a_ => @or_introl $d $hb ($p h1_ a_)
              | @or_intror _ _ b_ => @or_intror $d $hb b_
              end) 
        in (d', p')
      (* F∨2. *)
      else if Int.equal i 2 then 
        let (d, p) := forward h1 sub1 hb sub2 choices kind in 
        let d' := '($ha \/ $d) in 
        let p' := 
          '(fun (h1_ : $h1) (h2_ : $h2) => 
              match h2_ with 
              | @or_introl _ _ a_ => @or_introl $ha $d a_
              | @or_intror _ _ b_ => @or_intror $ha $d ($p h1_ b_)
              end) 
        in (d', p')
           else Control.throw (InteractFailure "[forward] F∨ rule : invalid index")
    (* Fnot *)
    | (not ?ha) => 
      if Int.equal i 0 then 
        let (d, p) := back h1 sub1 ha sub2 choices kind in 
        let d' := '(not $d) in 
        let p' := '(fun (h1_ : $h1) (h2_ : $h2) (d_ : $d) => h2_ ($p h1_ d_)) in
        (d', p')
           else Control.throw (InteractFailure "[forward] Fnot rule : invalid index")
    (* F⇒. *)
    | ?ha -> ?hb => 
      (* F⇒1. *)
      if Int.equal i 0 then 
        let (d, p) := back h1 sub1 ha sub2 choices kind in 
        let d' := '($d -> $hb) in 
        let p' := '(fun (h1_ : $h1) (h2_ : $h2) (d_ : $d) => h2_ ($p h1_ d_)) in
        (d', p')
      (* F⇒2. *)
      else if Int.equal i 1 then 
        let (d, p) := forward h1 sub1 hb sub2 choices kind in 
        let d' := '($ha -> $d) in
        let p' := '(fun (h1_ : $h1) (h2_ : $h2) (a_ : $ha) => $p h1_ (h2_ a_)) in
        (d', p')
      else Control.throw (InteractFailure "[forward] F⇒ rule : invalid index")
    | _ => Control.throw (InteractFailure 
      "[forward] unexpected head constructor for [Side Right]")
    end
  (****************************************************************************)
  (* Binder, instantiated. *)
  (****************************************************************************)
  | Binder Right (Some w) :: choices, sub1, 1 :: sub2, _ => 
    lazy_match! h2 with 
    (* F∀i. *)
    | forall x : ?ha, @?hb x => 
      let (d, p) := forward h1 sub1 '($hb $w) sub2 choices kind in 
      let p' := '(fun (h1_ : $h1) (xb_ : forall x, $hb x) => $p h1_ (xb_ $w)) in
      (d, p')
    | _ => Control.throw (InteractFailure 
      "[back] unexpected head constructor for [Binder Left (Some _)]")
    end
  (****************************************************************************)
  (* Binder, non-instantiated. *)
  (****************************************************************************)
  | Binder Right None :: choices, sub1, 1 :: sub2, _ =>
    lazy_match! h2 with 
    (* F∀s. *)
    | forall x : ?ha, @?hb x => 
      let x := Option.default @x (binder_name hb) in 
      let ev := fresh_evar (Some x) (Some ha) in
      let ev_constr := mk_var ev in
      let (d, p) := forward h1 sub1 '($hb $ev_constr) sub2 (apply_choices choices ev_constr) kind in
      let d := abstract_ident ev d in
      let p := abstract_ident ev p in
      let d' := fun_to_forall (Some x) d in
      let p' := '(fun (h1_ : $h1) (xb_ : $h2) (x : $ha) => ($p x) h1_ (xb_ x)) in
      (* Don't forget to clear the evar. *)
      Std.clear [ ev ] ; (d', p')
    (* F∃s. *)
    | exists x : ?ha, @?hb x => 
      let x := Option.default @x (binder_name hb) in 
      let ev := fresh_evar (Some x) (Some ha) in
      let ev_constr := mk_var ev in
      let (d, p) := forward h1 sub1 '($hb $ev_constr) sub2 (apply_choices choices ev_constr) kind in
      let d := abstract_ident ev d in
      let p := abstract_ident ev p in
      let d' := '(ex $d) in
      (* p x : h1 -> hb x -> d x *)
      let p' := 
        '(fun (h1_ : $h1) (xb_ : $h2) => 
            match xb_ with 
            | ex_intro _ x0 bx0 => ex_intro $d x0 (($p x0) h1_ bx0)
            end)
      in
      (* Don't forget to clear the evar. *)
      Std.clear [ ev ] ; (d', p')  
    | _ => Control.throw (InteractFailure 
      "[forward] unexpected head constructor for [Binder Right None]")
    end
  (****************************************************************************)
  (* Swap sides. *)
  (****************************************************************************)
  | Swap :: choices, _, _ , _ =>
    (* We have to adapt the proof : proving h1 -> h2 -> d is not the same as h2 -> h1 -> d. *)
    let (d, p) := forward h2 sub2 h1 sub1 choices (swap_dnd_kind kind) in 
    let swap := '(fun (p : $h2 -> $h1 -> $d) h1 h2 => p h2 h1) in
    (d, '($swap $p))
  | (Side Left :: _, _, _, _) =>
     let choices := swap_choices choices in
     let kind := swap_dnd_kind kind in
     let (d, p) := forward h2 sub2 h1 sub1 choices kind in
     let swap := '(fun (p : $h2 -> $h1 -> $d) h1 h2 => p h2 h1) in
    (d, '($swap $p))
  (* Eventually these rules should be removed. *)
  | (Binder Left _ :: _, _, _, _) => Control.throw (InteractFailure "[forward]: TODO swap ! ")
  (****************************************************************************)
  (* No matching rule. *)
  (****************************************************************************)
  | _ => Control.throw (InteractFailure "[forward] no matching rule")
  end.

(* 
Lemma not_lnot : not = lock_not.
  reflexivity.
Qed.
Lemma lnot_not : lock_not = not.
  reflexivity.
Qed.
Opaque lock_not.
*)

(* A thin wrapper around [back] that takes care of updating the proof state. *)
Ltac2 back_wrapper (hname : ident) subh subc choices kind : unit := 
  (* Fetch the hypothesis and conclusion. *)
  let h := Control.hyp hname in 
  let concl := Control.goal () in
  (* Perform the deep interaction. *)
  let (new_concl, proof) := back (Constr.type h) subh concl subc choices kind in
  (* Apply the proof to change the goal. *)
  refine '($proof $h _) ; 
  (* The type of the new goal comes from [proof] : we prefer to use [new_concl]. *)
  change $new_concl.

(* A thin wrapper around [forward] that takes care of updating the proof state.
   It takes as input the name of the new hypothesis to create. *)
Ltac2 forward_wrapper (hname1 : ident) sub1 (hname2 : ident) sub2 (hnew : ident) choices kind : unit := 
  (* Fetch the hypotheses. *)
  let h1 := Control.hyp hname1 in 
  let h2 := Control.hyp hname2 in 
  (* Perform the deep interaction. *)
  let (h3, proof) := forward (Constr.type h1) sub1 (Constr.type h2) sub2 choices kind in 
  (* Create the new hypothesis. *)
  pose ($proof $h1 $h2) as $hnew ; 
  (* We are only interested in the type of the new hypothesis. *)
  Std.clearbody [ hnew ] ; 
  (* The type of the new hypothesis comes from [proof] : we prefer to use [h3],
     which the same modulo conversion but may be better formatted (e.g. it might 
     have better variable names). *)
  change $h3 in $hnew.


