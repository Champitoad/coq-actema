open Utils.Pervasive
open Api
open Proofview
open CoqUtils
open Translate
open Ltac2_plugin

exception UnsupportedAction of Logic.action * string

(** Return the kernel name of a tactic defined in [Actema.HOL]. *)
let tactic_kname = kername [ "Actema"; "HOL" ]

(** This module deals with calling Ltac2 functions from Ocaml.
    
    See https://coq.zulipchat.com/#narrow/stream/237656-Coq-devs-.26-plugin-devs/topic/Ltac2.20FFI.20.3A.20building.20types.20and.20constructors
    for an explanation of how Ltac2 values are represented.
*)
module FFI = struct
  (** [calltac ~file name args] calls the Ltac2 tactic [name] with arguments [args], 
      and discards the result. 
      [file] is the name of the file (without the .v extension) the tactic is defined in. *)
  let calltac ~(file : string) (name : string) (args : Tac2val.valexpr list) :
      unit PVMonad.t =
    let open PVMonad in
    (* Debug *)
    (*let globals = Tac2env.globals () |> Names.KNmap.bindings in
      Log.printf "AAA count = %d" (List.length globals);
      List.iter (Log.printf "  %s" <<< Names.KerName.to_string <<< fst) globals;*)
    (* Construct the kernel name of the tactic. *)
    let kname = kername [ "Actema"; file ] name in
    (* Find the corresponding Ltac2 value. *)
    let tac =
      try Tac2interp.eval_global kname
      with Not_found ->
        failwith
        @@ Format.sprintf "Actions.FFI.calltac : unknown tactic name %s"
             (Names.KerName.to_string kname)
    in
    (* Call the tactic with its arguments. *)
    Tac2ffi.to_unit <$> Tac2val.apply_val tac args

  (** Encode an [Interact.side] to the Ltac2 type [DnD.side]. *)
  let of_side : Interact.side -> Tac2val.valexpr = function
    | Left -> Tac2val.ValInt 0
    | Right -> Tac2val.ValInt 1

  (** [of_choice import_term choice] encodes [choice] to the Ltac2 type [DnD.choice]. *)
  let of_choice (import_term : Lang.Term.t -> EConstr.t) :
      Interact.choice -> Tac2val.valexpr = function
    | Swap -> Tac2val.ValInt 0
    | Side side -> Tac2val.ValBlk (0, [| of_side side |])
    | Binder (side, SFlex) | Binder (side, SRigid) ->
        let none = Tac2val.ValInt 0 in
        Tac2val.ValBlk (1, [| of_side side; none |])
    | Binder (side, SBound witness) ->
        let constr = import_term witness in
        let some_witness = Tac2val.ValBlk (0, [| Tac2ffi.of_constr constr |]) in
        Tac2val.ValBlk (1, [| of_side side; some_witness |])

  (** [of_dnd_kind kind] encodes [kind] to the Ltac2 type [DnD.dnd_kind]. *)
  let of_dnd_kind : Logic.dnd_kind -> Tac2val.valexpr = function
    | Subform -> Tac2val.ValInt 0
    | RewriteL -> Tac2val.ValBlk (0, [| of_side Left |])
    | RewriteR -> Tac2val.ValBlk (0, [| of_side Right |])
end

(** Simplify the conclusion in the current Coq goal. *)
let simplify_goal () : unit tactic =
  (* We call Benjamin's tactic in HOL.v. *)
  calltac (tactic_kname "simplify_goal") []

(** Simplify the given hypothesis in the current Coq goal. *)
let simplify_hyp (hyp : Names.Id.t) : unit tactic =
  (* We call Benjamin's tactic in HOL.v. *)
  calltac (tactic_kname "simplify_hyp") [ EConstr.mkVar hyp ]

(** Make an introduction pattern to introduce named variables.
    If any of the given names is already bound, this will create a fresh name instead. *)
let mk_intro_patterns (names : string list) : Tactypes.intro_patterns =
  let open Tactypes in
  List.map
    (fun name ->
      CAst.make @@ IntroNaming (Namegen.IntroFresh (Names.Id.of_string name)))
    names

(** [convert_path coq_goal path] converts the path [path] from 
    the actema format to the format that the tactics expect. 
    
    The differences between these two formats are : 
    - In Actema existential quantification [exists x : ty, body] is represented 
      as [App (Cst ex, [ty; Lambda (x, ty, body)])], but the tactics work with first-class 
      existentials. For instance when pointing to [ty] or [body] in [exists x : ty, body],
      in Actema we use [[2; 0]] or [[2; 1]], but the tactics expect [[0]] or [[1]].
    - In Actema negation is represented as [App (Cst not, x)] and in Coq it is represented 
      as [Prod (_, x, False)].  *)
let rec convert_sub (term : Lang.Term.t) sub =
  match (sub, term) with
  | [], _ -> []
  (* Handle existential quantification. *)
  | 2 :: 0 :: sub, App (_, Cst ex, [ _; Lambda (_, x, ty, body) ])
    when Name.equal ex Lang.Constants.ex ->
      0 :: convert_sub body sub
  | 2 :: 1 :: sub, App (_, Cst ex, [ _; Lambda (_, x, ty, body) ])
    when Name.equal ex Lang.Constants.ex ->
      1 :: convert_sub body sub
  (* Handle negation. *)
  | 1 :: sub, App (_, Cst not, [ x ]) when Name.equal not Lang.Constants.not ->
      0 :: convert_sub x sub
  (* Lambdas and products. *)
  | 0 :: sub, Lambda (_, x, ty, body) | 0 :: sub, Prod (_, x, ty, body) ->
      0 :: convert_sub ty sub
  | 1 :: sub, Lambda (_, x, ty, body) | 1 :: sub, Prod (_, x, ty, body) ->
      1 :: convert_sub body sub
  (* Applications *)
  | i :: sub, App (_, f, args) when 0 <= i && i <= List.length args ->
      i :: convert_sub (List.at (f :: args) i) sub
  (* This should not happen. *)
  | _ -> failwith "Actions.convert_sub : invalid path"

let convert_path (coq_goal : Goal.t) (path : Logic.Path.t) : int list =
  (* Get the actema term the path points to. *)
  let api_goal = Export.goal coq_goal in
  let term =
    match path.kind with
    | Concl -> api_goal.g_concl
    | Hyp name -> (Logic.Hyps.by_name api_goal.g_hyps name).h_form
    | _ ->
        failwith
          "Actions.convert_path : can't handle paths that point to a variable."
  in
  (* Convert the path. *)
  convert_sub term path.sub

(** Turn an actema path into a Coq term of type [list nat] that can be fed to the old tactics in HOL.v.
    Takes as an optional argument a suffix to add to the path after it has been translated. *)
let compile_path ?(suffix = []) coq_goal (path : Logic.Path.t) : EConstr.t =
  let open Logic in
  let api_goal = Export.goal coq_goal in
  let term =
    match path.kind with
    | Concl -> api_goal.g_concl
    | Hyp name -> (Logic.Hyps.by_name api_goal.g_hyps name).h_form
    | _ ->
        failwith
          "Actions.compile_path : can't handle paths that point to a variable."
  in
  let sub = convert_sub term path.sub in
  Trm.Datatypes.natlist (Goal.env coq_goal) (sub @ suffix)

(*********************************************************************************)
(** [AIntro] actions. *)
(*********************************************************************************)

(** Execute an [AIntro] action. *)
let execute_aintro (coq_goal : Goal.t) side : unit tactic =
  let open Lang in
  let open Term in
  let api_goal = Export.goal coq_goal in
  match (api_goal.g_concl, side) with
  | Cst true_, 0 when Name.equal true_ Constants.true_ ->
      Tactics.one_constructor 1 Tactypes.NoBindings
  | Prod (_, x, ty, body), 0 when not (Term.contains_loose_bvars body) ->
      let pat = mk_intro_patterns [ "h" ] in
      Tactics.intro_patterns false pat
  | App (_, Cst not_, _), 0 when Name.equal not_ Constants.not ->
      let pat = mk_intro_patterns [ "h" ] in
      Tactics.intro_patterns false pat
  | App (_, Cst and_, _), 0 when Name.equal and_ Constants.and_ ->
      Tactics.split Tactypes.NoBindings
  | App (_, Cst equiv, _), 0 when Name.equal equiv Constants.equiv ->
      Tactics.split Tactypes.NoBindings
  | App (_, Cst or_, _), 0 when Name.equal or_ Constants.or_ ->
      Tactics.left Tactypes.NoBindings
  | App (_, Cst or_, _), 1 when Name.equal or_ Constants.or_ ->
      Tactics.right Tactypes.NoBindings
  | Prod (_, x, _, _), 0 ->
      let pat =
        match x with
        | Anonymous -> mk_intro_patterns [ "x" ]
        | Named name -> mk_intro_patterns [ Name.show name ]
      in
      Tactics.intro_patterns false pat
  | App (_, Cst eq, _), 0 when Name.equal eq Constants.eq ->
      (* Here we are not sure that the two sides of the equality are indeed equal.

         The frontend can only handle syntactic equality : it delegates to the plugin
         the responsability of dealing with non-equal terms.

         We choose to simply ignore an intro action on an equality that is not provable by computation. *)
      Tacticals.tclTRY Tactics.reflexivity
  | _ ->
      let msg =
        "The goal has an invalid head connective/predicate for an introduction."
      in
      raise @@ UnsupportedAction (Logic.AIntro side, msg)

(*********************************************************************************)
(** [AElim] actions. *)
(*********************************************************************************)

(** Execute an [AElim] action. This action eliminates the hypothesis named [hyp_name].
    The hypothesis is cleared and replaced by (possibly several) goals which contain derived hypotheses.
    The integer index is used when eliminating an equality, to decide which way (left/right) to rewrite. *)
let execute_aelim (coq_goal : Goal.t) hyp_name i : unit tactic =
  let open Lang in
  let open Term in
  let api_goal = Export.goal coq_goal in
  let hyp_id = Names.Id.of_string @@ Name.show hyp_name in
  let hyp = Logic.Hyps.by_name api_goal.g_hyps hyp_name in
  match hyp.h_form with
  | Cst c when Name.equal c Constants.true_ || Name.equal c Constants.false_ ->
      let bindings = (EConstr.mkVar hyp_id, Tactypes.NoBindings) in
      Tactics.default_elim false (Some true) bindings
  | App (_, Cst not_, _) when Name.equal not_ Constants.not ->
      let bindings = (EConstr.mkVar hyp_id, Tactypes.NoBindings) in
      Tactics.default_elim false (Some true) bindings
  | Prod (_, x, ty, body) when not (Term.contains_loose_bvars body) ->
      Tactics.apply @@ EConstr.mkVar hyp_id
  | App (_, Cst c, _)
    when Name.equal c Constants.and_ || Name.equal c Constants.equiv ->
      (* First eliminate the hypothesis, then introduce the hypotheses we created. *)
      let bindings = (EConstr.mkVar hyp_id, Tactypes.NoBindings) in
      Tacticals.tclTHENS
        (Tactics.default_elim false (Some true) bindings)
        [ Tactics.intro_patterns false
          @@ mk_intro_patterns [ Name.show hyp_name; Name.show hyp_name ]
        ]
  | App (_, Cst or_, _) when Name.equal or_ Constants.or_ ->
      (* First eliminate the hypothesis, then introduce the hypotheses we created. *)
      let bindings = (EConstr.mkVar hyp_id, Tactypes.NoBindings) in
      Tacticals.tclTHENS
        (Tactics.default_elim false (Some true) bindings)
        [ Tactics.intro_patterns false
          @@ mk_intro_patterns [ Name.show hyp_name ]
        ; Tactics.intro_patterns false
          @@ mk_intro_patterns [ Name.show hyp_name ]
        ]
  | App (_, Cst ex, [ _; Lambda (_, x, _, _) ]) when Name.equal ex Constants.ex
    ->
      (* First eliminate the hypothesis, then introduce the variable and hypothesis we created. *)
      let bindings = (EConstr.mkVar hyp_id, Tactypes.NoBindings) in
      let var_name =
        match x with Anonymous -> "x" | Named name -> Name.show name
      in
      Tacticals.tclTHENS
        (Tactics.default_elim false (Some true) bindings)
        [ Tactics.intro_patterns false
          @@ mk_intro_patterns [ var_name; Name.show hyp_name ]
        ]
  | App (_, Cst eq, [ _; _; _ ]) when Name.equal eq Constants.eq && i = 0 ->
      FFI.calltac ~file:"Misc" "rew_all_left" [ Tac2ffi.of_ident hyp_id ]
  | App (_, Cst eq, [ _; _; _ ]) when Name.equal eq Constants.eq && i = 1 ->
      FFI.calltac ~file:"Misc" "rew_all_right" [ Tac2ffi.of_ident hyp_id ]
  | _ ->
      let msg = "Could not apply elimination action." in
      raise @@ UnsupportedAction (Logic.AElim (hyp_name, i), msg)

(*********************************************************************************)
(** [ALemmaAdd] actions. *)
(*********************************************************************************)

(** Execute an [ALemmaAdd] action. This consists in adding the required lemma as a hypothesis. *)
let execute_alemma_add coq_goal lemma_name =
  (* Get the Coq term that corresponds to the lemma. *)
  let symbol_table = Symbols.all coq_goal in
  let hyp_form =
    match Symbols.Table.find_opt lemma_name symbol_table with
    | Some symbol -> Symbols.to_econstr coq_goal symbol
    | None ->
        raise
        @@ UnsupportedAction
             (ALemmaAdd lemma_name, "This lemma does not exist !")
  in
  (* Add the new hypothesis. *)
  let basename =
    lemma_name |> Name.show |> String.split_on_char '.' |> List.last
  in
  let hyp_name = Names.Name.mk_name @@ Goal.fresh_name ~basename coq_goal () in
  Tactics.pose_proof hyp_name hyp_form

(*********************************************************************************)
(** [ADnD] actions. *)
(*********************************************************************************)

(** Abstract an itrace i.e. change all the instantiation witnesses from : 
    - having FVars 
    to : 
    - having BVars 
    - binding these BVars by Lambdas 
*)
let abstract_itrace itrace context : Interact.choice list =
  let open Lang in
  let open Interact in
  (* [close_one witness fvar] closes the witness with respect to the free variable [fvar],
     i.e. it replaces [fvar] by [BVar 0] and binds this BVar with a lambda. *)
  let close_one witness fvar =
    let entry = Option.get @@ Context.find fvar context in
    Term.mkLambda entry.binder entry.type_ (Term.abstract fvar witness)
  in
  (* The list [passed] contains the *uninstantiated* free variables bound above,
     the most recently bound first. *)
  let rec loop passed = function
    (* Swap sides. *)
    | Swap :: choices, fvars1, fvars2 ->
        Swap :: loop passed (choices, fvars2, fvars1)
    (* Simply descend on a side or another. *)
    | Side side :: choices, fvars1, fvars2 ->
        Side side :: loop passed (choices, fvars1, fvars2)
    (* Traverse a binder with instantiating. *)
    | Binder (Left, SBound witness) :: choices, v1 :: fvars1, fvars2 ->
        Binder (Left, SBound (List.fold_left close_one witness passed))
        :: loop passed (choices, fvars1, fvars2)
    | Binder (Right, SBound witness) :: choices, fvars1, v2 :: fvars2 ->
        Binder (Right, SBound (List.fold_left close_one witness passed))
        :: loop passed (choices, fvars1, fvars2)
    (* Traverse a binder without instantiating. *)
    | Binder (Left, sitem) :: choices, v1 :: fvars1, fvars2 ->
        Binder (Left, sitem) :: loop (v1 :: passed) (choices, fvars1, fvars2)
    | Binder (Right, sitem) :: choices, fvars1, v2 :: fvars2 ->
        Binder (Right, sitem) :: loop (v2 :: passed) (choices, fvars1, fvars2)
    (* Finished. *)
    | [], [], [] -> []
    (* Errors. *)
    | _ -> Log.error "Actions.abstract_itrace : unexpected case"
  in
  loop [] itrace

(* Helper function to remove the last index in a path. *)
let remove_last (path : Logic.Path.t) : Logic.Path.t =
  let sub = List.remove_at (List.length path.sub - 1) path.sub in
  { path with sub }

(** Helper function to swap the two sides of the link in a [dnd_kind]. *)
let opp_dnd_kind : Logic.dnd_kind -> Logic.dnd_kind = function
  | Subform -> Logic.Subform
  | RewriteL -> RewriteR
  | RewriteR -> RewriteL

(** Helper function to swap the two sides of the link in a [choice]. *)
let opp_choice : Interact.choice -> Interact.choice = function
  | Swap -> Swap
  | Side side -> Side (Interact.opp_side side)
  | Binder (side, witness) -> Binder (Interact.opp_side side, witness)

(** Precondition : [src] and [dst] point to a hypothesis or the conclusion,
    and can't both point to the conclusion. *)
let execute_adnd coq_goal src dst (unif_data : Logic.unif_data) dnd_kind :
    unit tactic =
  let open PVMonad in
  let pregoal = Export.goal coq_goal in
  (* Perform deep interaction (i.e. choose an order of application of the rewrite rules). *)
  let itrace =
    Interact.dlink dnd_kind (src, unif_data.fvars_1) (dst, unif_data.fvars_2)
      unif_data.subst pregoal
  in
  (* Abstract the instantiations. *)
  let choices = abstract_itrace itrace unif_data.context in
  Log.printf "CHOICES %s" (List.to_string Interact.show_choice choices);
  (* Export the Coq symbols to translate Actema terms to Coq terms later on. *)
  let symbols = Symbols.all coq_goal in
  (* Call the Ltac2 tactic to do the rest of the work. *)
  match (src.kind, dst.kind) with
  | Hyp h1, Hyp h2 ->
      let hnew = Goal.fresh_name ~basename:(Name.show h2) coq_goal () in
      let h1 = Names.Id.of_string_soft @@ Name.show h1 in
      let h2 = Names.Id.of_string_soft @@ Name.show h2 in
      FFI.calltac ~file:"DnD" "forward_wrapper"
        [ Tac2ffi.of_ident h1
        ; Tac2ffi.(of_list of_int) @@ convert_path coq_goal src
        ; Tac2ffi.of_ident h2
        ; Tac2ffi.(of_list of_int) @@ convert_path coq_goal dst
        ; Tac2ffi.of_ident hnew
        ; Tac2ffi.of_list (FFI.of_choice (Import.term coq_goal symbols)) choices
        ; FFI.of_dnd_kind dnd_kind
        ]
      >> simplify_hyp hnew
  | Hyp h, Concl ->
      let h = Names.Id.of_string_soft @@ Name.show h in
      FFI.calltac ~file:"DnD" "back_wrapper"
        [ Tac2ffi.of_ident h
        ; Tac2ffi.(of_list of_int) @@ convert_path coq_goal src
        ; Tac2ffi.(of_list of_int) @@ convert_path coq_goal dst
        ; Tac2ffi.of_list (FFI.of_choice (Import.term coq_goal symbols)) choices
        ; FFI.of_dnd_kind dnd_kind
        ]
      >> simplify_goal ()
  | Concl, Hyp h ->
      (* The tactic [back_wrapper] expects the hypothesis on the left
         and the conclusion on the right : we have to swap the two sides of the link. *)
      let h = Names.Id.of_string_soft @@ Name.show h in
      FFI.calltac ~file:"DnD" "back_wrapper"
        [ Tac2ffi.of_ident h
        ; Tac2ffi.(of_list of_int) @@ convert_path coq_goal dst
        ; Tac2ffi.(of_list of_int) @@ convert_path coq_goal src
        ; Tac2ffi.of_list (FFI.of_choice (Import.term coq_goal symbols))
          @@ List.map opp_choice choices
        ; FFI.of_dnd_kind @@ opp_dnd_kind dnd_kind
        ]
      >> simplify_goal ()
  | _ -> assert false

(*********************************************************************************)
(** [AInstantiate] actions. *)
(*********************************************************************************)

let execute_ainstantiate coq_goal witness (path : Logic.Path.t) : unit tactic =
  (* failwith "ainstantiate: TODO" *)

  (* Compile the witness. *)
  let table = Symbols.all coq_goal in
  let coq_witness = Import.term coq_goal table witness in
  (* Compile the path. *)
  (* The tactics expect the path to end with a [1], i.e. to point to the body
     of the quantifier that is instantiated. *)
  let coq_path = compile_path ~suffix:[ 1 ] coq_goal path in
  match path.kind with
  | Hyp name ->
      let id = EConstr.mkVar @@ Names.Id.of_string @@ Name.show name in
      let new_id =
        EConstr.mkVar @@ Goal.fresh_name ~basename:(Name.show name) coq_goal ()
      in
      calltac
        (tactic_kname "dyn_inst_hyp")
        [ coq_path; id; new_id; coq_witness ]
  | Concl -> calltac (tactic_kname "dyn_inst_goal") [ coq_path; coq_witness ]
  | VarHead _ | VarBody _ | VarType _ ->
      raise
      @@ UnsupportedAction
           (AInstantiate (witness, [ path ]), "Can't instantiate in variable")

(*********************************************************************************)
(** Putting it all together. *)
(*********************************************************************************)

let execute_helper (action : Logic.action) (coq_goal : Goal.t) : unit tactic =
  let open PVMonad in
  match action with
  | Logic.AId -> Tacticals.tclIDTAC
  | Logic.ADuplicate hyp_name ->
      let hyp_name = Name.show hyp_name in
      let new_name =
        Goal.fresh_name ~basename:hyp_name coq_goal () |> Names.Name.mk_name
      in
      let hyp = EConstr.mkVar @@ Names.Id.of_string hyp_name in
      Tactics.pose_proof new_name hyp
  | Logic.AClear hyp_name ->
      Tactics.clear [ Names.Id.of_string @@ Name.show hyp_name ]
  | Logic.AExact name ->
      let name = Names.Id.of_string @@ Name.show name in
      Tactics.exact_check (EConstr.mkVar name)
  | Logic.AGeneralize name ->
      let name = Names.Id.of_string @@ Name.show name in
      Generalize.generalize_dep (EConstr.mkVar name)
  | Logic.AIntro side -> execute_aintro coq_goal side
  | Logic.AElim (hyp_name, i) -> execute_aelim coq_goal hyp_name i
  | Logic.ALemmaAdd full_name -> execute_alemma_add coq_goal full_name
  | Logic.ADnD (src, dst, unif_data, dnd_kind) ->
      execute_adnd coq_goal src dst unif_data dnd_kind
  | Logic.ASimpl path -> begin
      match path.kind with
      | Hyp name ->
          let id = Names.Id.of_string @@ Name.show name in
          let sub = convert_path coq_goal path in
          FFI.calltac ~file:"Misc" "deep_simpl_hyp"
            [ Tac2ffi.of_ident id; Tac2ffi.(of_list of_int) sub ]
	     >> simplify_hyp id
      | Concl ->
          let sub = convert_path coq_goal path in
          FFI.calltac ~file:"Misc" "deep_simpl_concl"
            [ Tac2ffi.(of_list of_int) sub ]
	    >> simplify_goal ()
      | VarHead _ | VarBody _ | VarType _ ->
          raise @@ UnsupportedAction (action, "Can't simplify in variable")
    end
  | Logic.ACase term ->
      let symbol_table = Symbols.all coq_goal in
      let coq_term = Import.term coq_goal symbol_table term in
      FFI.calltac ~file:"Misc" "mydestruct" [ Tac2ffi.of_constr coq_term ]
  | Logic.AInd term ->
      let symbol_table = Symbols.all coq_goal in
      let coq_term = Import.term coq_goal symbol_table term in
      FFI.calltac ~file:"Misc" "myinduction" [ Tac2ffi.of_constr coq_term ]
  | Logic.ACaseIntro n ->
      (* Introduce (n-1) variables/hypotheses. *)
      repeatM (n - 1) Tactics.intro
      (* Destruct the last variable. *)
      >> Tactics.intro_then @@ fun name ->
         FFI.calltac ~file:"Misc" "mydestruct"
           [ Tac2ffi.of_constr @@ EConstr.mkVar name ]
  | Logic.AIndIntro n ->
      (* Introduce (n-1) variables/hypotheses. *)
      repeatM (n - 1) Tactics.intro
      (* Induction on the last variable. *)
      >> Tactics.intro_then @@ fun name ->
         FFI.calltac ~file:"Misc" "myinduction"
           [ Tac2ffi.of_constr @@ EConstr.mkVar name ]
  | Logic.AInstantiate (witness, quants) ->
      (* Instantiate the quantifiers one by one.
         TODO : this might break if instantiating a quantifier changes the paths to other
         instantiated quantifiers.
         Maybe instantiating the deepest quantifiers first fixes this ? *)
      mapM_ (execute_ainstantiate coq_goal witness) quants

let execute ((idx, a) : int * Logic.action) : unit tactic =
  tclFOCUS (idx + 1) (idx + 1) @@ Goal.enter @@ execute_helper a
