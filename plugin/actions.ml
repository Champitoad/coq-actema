open Utils.Pervasive
open Api
open Proofview
open CoqUtils
open Translate

exception UnsupportedAction of Logic.action * string

(** Return the kernel name of a tactic defined in [Actema.HOL]. *)
let tactic_kname = kername [ "Actema"; "HOL" ]

(** Make an introduction pattern to introduce named variables.
    If any of the given names is already bound, this will create a fresh name instead. *)
let mk_intro_patterns (names : string list) : Tactypes.intro_patterns =
  let open Tactypes in
  List.map
    (fun name ->
      CAst.make @@ IntroNaming (Namegen.IntroFresh (Names.Id.of_string name)))
    names

(** Turn a list of [Interact.choice] into a Coq term of type [list bool] 
    that can be fed to tactics. *)
let compile_sides coq_goal choices : EConstr.t =
  let open Interact in
  choices
  |> List.map (function Side side | Binder (side, _) -> side)
  |> List.map (function Left -> false | Right -> true)
  |> Trm.Datatypes.boollist (Goal.env coq_goal)

(** Turn a list of [Interact.choice] into a Coq term of type [list option DYN] 
    that can be fed to tactics. *)
let compile_instantiations coq_goal choices : EConstr.t =
  let open Interact in
  let env = Goal.env coq_goal in
  let sigma = Goal.sigma coq_goal in
  let symbol_table = Symbols.all coq_goal in
  (* Coq's [DYN] type. *)
  let dyn = Trm.mkInd env [ "Actema"; "HOL" ] "DYN" in
  (* Coq's [option DYN] type. *)
  let opt_dyn = Trm.Datatypes.option env dyn in
  (* Coq's [mDYN] constructor. *)
  let mdyn =
    Trm.mkConstruct ~constructor:1 (Goal.env coq_goal) [ "Actema"; "HOL" ] "DYN"
  in
  (* Wrap a Coq term in a [DYN]. *)
  let mkDyn (econstr : EConstr.t) : EConstr.t =
    let ty = Retyping.get_type_of env sigma econstr in
    EConstr.mkApp (mdyn, [| ty; econstr |])
  in
  (* We are only interested in the choices for instantiable binders. *)
  choices
  |> List.filter_map (function
       | Binder (_, SFlex) -> Some None
       | Binder (_, SBound witness) -> Some (Some witness)
       | _ -> None)
  |> Trm.Datatypes.of_list (Goal.env coq_goal) opt_dyn
       (Trm.Datatypes.of_option env dyn
          (mkDyn <<< Import.term coq_goal symbol_table))

(** [convert_sub term sub] converts the path [sub] (that points inside [term])
    from the actema format to the format that the tactics expect. 
    
    The differences between these two formats are : 
    - In Actema applications are n-ary, whereas the tactics expect applications to
      be binary. For instance when pointing to [x] in [f x y z], in Actema
      we use [[1]] but the tactics expect [[0; 0; 1]]. 
    - In Actema existential quantification [exists x : ty, body] is represented 
      as [App (Cst ex, [ty; Lambda (x, ty, body)])], but the tactics work with first-class 
      existentials. For instance when pointing to [ty] or [body] in [exists x : ty, body],
      in Actema we use [[2; 0]] or [[2; 1]], but the tactics expect [[0]] or [[1]]. *)
let rec convert_sub (term : Lang.Term.t) (sub : int list) : int list =
  match (sub, term) with
  | [], _ -> []
  (* Lambdas and products don't change. *)
  | 0 :: sub, Lambda (_, x, ty, body) | 0 :: sub, Prod (_, x, ty, body) ->
      0 :: convert_sub ty sub
  | 1 :: sub, Lambda (_, x, ty, body) | 1 :: sub, Prod (_, x, ty, body) ->
      1 :: convert_sub body sub
  (* Handle existential quantification. *)
  | 2 :: 0 :: sub, App (_, Cst ex, [ _; Lambda (_, x, ty, body) ])
    when Name.equal ex Lang.Constants.ex ->
      0 :: convert_sub body sub
  | 2 :: 1 :: sub, App (_, Cst ex, [ _; Lambda (_, x, ty, body) ])
    when Name.equal ex Lang.Constants.ex ->
      1 :: convert_sub body sub
  (* Turn n-ary applications to binary applications. *)
  (* One argument. *)
  | 0 :: sub, App (_, f, [ arg ]) -> 0 :: convert_sub f sub
  | 1 :: sub, App (_, f, [ arg ]) -> 1 :: convert_sub arg sub
  (* At least two arguments. *)
  | n :: sub, App (_, f, args) when n = List.length args ->
      1 :: convert_sub (List.last args) sub
  | n :: sub, App (_, f, args) when 0 <= n && n < List.length args ->
      let args = List.remove_at (List.length args - 1) args in
      0 :: convert_sub (Lang.Term.mkApps f args) (n :: sub)
  (* This should not happen. *)
  | _ -> failwith "Actions.convert_sub : invalid path"

(** Turn an actema path into a Coq term of type [list nat] that can be fed to tactics. *)
let compile_path coq_goal (path : Logic.Path.t) : EConstr.t =
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
  path.sub |> convert_sub term |> Trm.Datatypes.natlist (Goal.env coq_goal)

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
      calltac (tactic_kname "rew_all_left") [ EConstr.mkVar hyp_id ]
  | App (_, Cst eq, [ _; _; _ ]) when Name.equal eq Constants.eq && i = 1 ->
      calltac (tactic_kname "rew_all_right") [ EConstr.mkVar hyp_id ]
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
  (* Compute the de Bruijn index associated to the free variable [fvar].
     The lists [passed1] and [passed2] contain the free variables
     that are bound on each side so far, the most recently bound variable *first*. *)
  let fvar_index passed1 passed2 fvar : int =
    (* The variables are bound in the order fun x0 x1 x2 ... y0 y1 y2 ... => body,
       where passed1 = [x0; x1 ...] and passed2 = [y0; y1 ...].
       Thus we have to find the index of fvar in the *reverse* of passed1 @ passed2. *)
    match List.index_of fvar @@ List.rev (passed1 @ passed2) with
    | Some idx -> idx
    | None -> failwith "Actions.abstract_itrace: unbound free variable"
  in
  (* Close a witness, i.e. :
     - replace all FVars by BVars.
     - bind all loose BVars with Lambdas.
     The variables of [passed1] are bound *above* the variables of [passed2]. *)
  let close_witness passed1 passed2 witness =
    witness
    |> Term.fsubst (Term.mkBVar <<< fvar_index passed1 passed2)
    |> List.fold_right
         begin
           fun fvar body ->
             let entry = Option.get @@ Context.find fvar context in
             Term.mkLambda entry.Context.binder entry.Context.type_ body
         end
         (passed1 @ passed2)
  in
  let rec loop passed1 passed2 = function
    (* Simply descend on a side or another. *)
    | Side side :: choices, fvars1, fvars2 ->
        Side side :: loop passed1 passed2 (choices, fvars1, fvars2)
    (* Traverse a binder with instantiating. *)
    | Binder (Left, SBound witness) :: choices, v1 :: fvars1, fvars2 ->
        Binder (Left, SBound (close_witness passed1 passed2 witness))
        :: loop (v1 :: passed1) passed2 (choices, fvars1, fvars2)
    | Binder (Right, SBound witness) :: choices, fvars1, v2 :: fvars2 ->
        Binder (Right, SBound (close_witness passed1 passed2 witness))
        :: loop passed1 (v2 :: passed2) (choices, fvars1, fvars2)
    (* Traverse a binder without instantiating. *)
    | Binder (Left, sitem) :: choices, v1 :: fvars1, fvars2 ->
        Binder (Left, sitem)
        :: loop (v1 :: passed1) passed2 (choices, fvars1, fvars2)
    | Binder (Right, sitem) :: choices, fvars1, v2 :: fvars2 ->
        Binder (Right, sitem)
        :: loop passed1 (v2 :: passed2) (choices, fvars1, fvars2)
    | _ -> []
  in
  loop [] [] itrace

(* Helper function to remove the last index in a path. *)
let remove_last (path : Logic.Path.t) : Logic.Path.t =
  let sub = List.remove_at (List.length path.sub - 1) path.sub in
  { path with sub }

(** Precondition : [src] and [dst] respectively point to either :
    - two hypotheses.
    - a hypothesis and the conclusion.

    In particular we forbid the case where they point to : 
    - the conclusion and a hypothesis. *)
let execute_adnd coq_goal src dst (unif_data : Logic.unif_data) dnd_kind :
    unit tactic =
  let pregoal = Export.goal coq_goal in
  (* Perform deep interaction. *)
  let itrace =
    Interact.dlink (src, unif_data.fvars_1) (dst, unif_data.fvars_2)
      unif_data.subst pregoal
  in
  (* Abstract the instantiations. *)
  let choices = abstract_itrace itrace unif_data.context in
  (* Translate the choices to Coq. *)
  let coq_sides = compile_sides coq_goal choices in
  Log.printf "Substitution:\n%s\n" (Unif.show_subst unif_data.subst);
  (* Translate the instantiations to Coq. *)
  let coq_instantiations = compile_instantiations coq_goal choices in
  (* Call the appropriate tactic. *)
  match (dnd_kind, src.kind, dst.kind) with
  (* Subformula, hypothesis and conclusion. *)
  | Logic.Subform, Hyp hyp, Concl ->
      let hyp = EConstr.mkVar @@ Names.Id.of_string @@ Name.show hyp in
      calltac (tactic_kname "back")
        [ hyp
        ; compile_path coq_goal src
        ; compile_path coq_goal dst
        ; coq_sides
        ; coq_instantiations
        ]
  (* Subformula, two hypotheses. *)
  | Subform, Hyp hyp1, Hyp hyp2 ->
      let hyp1 = EConstr.mkVar @@ Names.Id.of_string @@ Name.show hyp1 in
      let hyp2 = EConstr.mkVar @@ Names.Id.of_string @@ Name.show hyp2 in
      let hyp3 = EConstr.mkVar @@ Goal.fresh_name ~basename:"H" coq_goal () in
      calltac (tactic_kname "forward")
        [ hyp1
        ; hyp2
        ; hyp3
        ; compile_path coq_goal src
        ; compile_path coq_goal dst
        ; coq_sides
        ; coq_instantiations
        ]
  (* Rewrite with a hypothesis in the goal. *)
  | RewriteL, Hyp hyp, Concl ->
      (*Log.printf "Sides : ";
        Log.econstr (Goal.env coq_goal) (Goal.sigma coq_goal) coq_sides;
        Log.printf "Source path : ";
        Log.econstr (Goal.env coq_goal) (Goal.sigma coq_goal)
          (compile_path coq_goal @@ remove_last src);
        Log.printf "Dest path : ";
        Log.econstr (Goal.env coq_goal) (Goal.sigma coq_goal)
          (compile_path coq_goal dst);
        Log.printf "Instantiations : ";
        Log.econstr (Goal.env coq_goal) (Goal.sigma coq_goal) coq_instantiations;*)
      let hyp = EConstr.mkVar @@ Names.Id.of_string @@ Name.show hyp in
      calltac (tactic_kname "rew_dnd")
        [ hyp
        ; compile_path coq_goal (remove_last src)
        ; compile_path coq_goal dst
        ; coq_sides
        ; coq_instantiations
        ]
  (* Rewrite with the goal in a hypothesis. *)
  | RewriteR, Hyp hyp, Concl ->
      let hyp = EConstr.mkVar @@ Names.Id.of_string @@ Name.show hyp in
      calltac
        (tactic_kname "rew_dnd_rev")
        [ hyp
        ; compile_path coq_goal src
        ; compile_path coq_goal (remove_last dst)
        ; coq_sides
        ; coq_instantiations
        ]
  (* Rewrite with a hypothesis in another hypothesis. *)
  | RewriteL, Hyp hyp1, Hyp hyp2 ->
      let hyp1 = EConstr.mkVar @@ Names.Id.of_string @@ Name.show hyp1 in
      let hyp2 = EConstr.mkVar @@ Names.Id.of_string @@ Name.show hyp2 in
      let hyp3 = EConstr.mkVar @@ Goal.fresh_name ~basename:"H" coq_goal () in
      calltac
        (tactic_kname "rew_dnd_hyp")
        [ hyp1
        ; hyp2
        ; hyp3
        ; compile_path coq_goal (remove_last src)
        ; compile_path coq_goal dst
        ; coq_sides
        ; coq_instantiations
        ]
  | _ ->
      raise
      @@ UnsupportedAction
           ( ADnD (src, dst, unif_data, dnd_kind)
           , "Invalid items for DnD action." )

(*********************************************************************************)
(** Putting it all together. *)
(*********************************************************************************)

(** [clear_if_var coq_goal econstr] checks if [econstr] is a local variable, 
    and if so clears it from the goal. *)
let clear_if_var coq_goal econstr : unit tactic =
  if EConstr.isVar (Goal.sigma coq_goal) econstr
  then
    let vname = EConstr.destVar (Goal.sigma coq_goal) econstr in
    Tactics.clear [ vname ]
  else Tacticals.tclIDTAC

(** [case_helper coq_goal econstr] performs case analysis on [econstr]. *)
let case_helper coq_goal econstr : unit tactic =
  let open PVMonad in
  Induction.destruct false (Some true) econstr None None
  (* For some reason [Induction.destruct] does not clear [econstr]. *)
  >> clear_if_var coq_goal econstr

(** [induction_helper coq_goal econstr] performs induction on [econstr]. *)
let induction_helper coq_goal econstr : unit tactic =
  let open PVMonad in
  Induction.induction false (Some true) econstr None None
  (* For some reason [Induction.induction] does not clear [econstr]. *)
  >> clear_if_var coq_goal econstr

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
      (* Helper function to swap the two sides of the link in a [dnd_kind]. *)
      let reverse_dnd = function
        | Logic.Subform -> Logic.Subform
        | RewriteL -> RewriteR
        | RewriteR -> RewriteL
      in
      (* Helper function to swap the two sides of the link in a [unif_data]. *)
      let reverse_unif (unif : Logic.unif_data) =
        { unif_data with fvars_1 = unif.fvars_2; fvars_2 = unif.fvars_1 }
      in
      begin
        (* Check the items are valid, and swap [src] and [dst] if needed
           to avoid redundant cases in [execute_adnd]. *)
        match (src.kind, dst.kind, dnd_kind) with
        | Concl, Hyp _, _ | Hyp _, Hyp _, RewriteR ->
            execute_adnd coq_goal dst src (reverse_unif unif_data)
              (reverse_dnd dnd_kind)
        | Hyp _, Hyp _, _ | Hyp _, Concl, _ ->
            execute_adnd coq_goal src dst unif_data dnd_kind
        | _ ->
            raise @@ UnsupportedAction (action, "Invalid items for DnD action.")
      end
  | Logic.ASimpl path -> begin
      match path.kind with
      | Hyp name ->
          let id = EConstr.mkVar @@ Names.Id.of_string @@ Name.show name in
          let path = compile_path coq_goal path in
          calltac (tactic_kname "simpl_path_hyp") [ id; path ]
      | Concl ->
          let path = compile_path coq_goal path in
          calltac (tactic_kname "simpl_path") [ path ]
      | VarHead _ | VarBody _ | VarType _ ->
          raise @@ UnsupportedAction (action, "Can't simplify in variable")
    end
  | Logic.ACase term ->
      let symbol_table = Symbols.all coq_goal in
      let coq_term = Import.term coq_goal symbol_table term in
      case_helper coq_goal coq_term
  | Logic.AInd term ->
      let symbol_table = Symbols.all coq_goal in
      let coq_term = Import.term coq_goal symbol_table term in
      induction_helper coq_goal coq_term
  | Logic.ACaseIntro n ->
      (* Introduce (n-1) variables/hypotheses. *)
      repeatM (n - 1) Tactics.intro
      (* Destruct the last variable. *)
      >> Tactics.intro_then @@ fun name ->
         case_helper coq_goal (EConstr.mkVar name)
  | Logic.AIndIntro n ->
      (* Introduce (n-1) variables/hypotheses. *)
      repeatM (n - 1) Tactics.intro
      (* Induction on the last variable. *)
      >> Tactics.intro_then @@ fun name ->
         induction_helper coq_goal (EConstr.mkVar name)

let execute ((idx, a) : int * Logic.action) : unit tactic =
  tclFOCUS (idx + 1) (idx + 1) @@ Goal.enter @@ execute_helper a
