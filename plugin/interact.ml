open Utils.Pervasive
open Api
open Lang
open Logic
open CoqUtils

type side = Left | Right [@@deriving show]

let opp_side = function Left -> Right | Right -> Left

type choice = Side of side | Binder of side * Unif.sitem [@@deriving show]
type itrace = choice list * FVarId.t list * FVarId.t list [@@deriving show]

(* For a backwards interaction, the first formula is the hypothesis,
   the second formula is the conclusion.
   For a forward interaction, the order doesn't matter. *)
type state =
  { (* The global environment we are working in. *)
    env : Env.t
  ; (* The local context we are working in. *)
    context : Context.t
  ; (* The first focussed subterm. This lives in [state.context]. *)
    t1 : Term.t
  ; (* The second focussed subterm. This lives in [state.context]. *)
    t2 : Term.t
  ; (* The remaining subpath in [t1]. *)
    sub1 : int list
  ; (* The remaining subpath in [t2]. *)
    sub2 : int list
  ; (* The remaining free variables identifiers in [t1].
       The outermost variable is first.
       These free variables are not yet in [state.context] : they are the names we
       need to use when adding new entries to the context. *)
    fvars_1 : FVarId.t list
  ; (* The remaining free variables identifiers in [t2]. *)
    fvars_2 : FVarId.t list
  ; (* The global substitution. This has domain :
       [domain context + fvars_1 + fvars_2]. *)
    subst : Unif.subst
  ; (* The choices generated so far. The most recent choice is first. *)
    choices : choice list
  }

(* Step into the left formula. *)
let left_step state ?(invert = false) ?(binder = None) t1 sub1 =
  match (binder : Context.entry option) with
  | None ->
      ({ state with choices = Side Left :: state.choices; t1; sub1 }, invert)
  | Some { binder; type_ } ->
      let fvar = List.hd state.fvars_1 in
      let context = Context.add fvar binder type_ state.context in
      let choice =
        Binder (Left, Option.get @@ Unif.get_sitem state.subst fvar)
      in
      ( { state with
          choices = choice :: state.choices
        ; context
        ; t1 = Term.instantiate fvar t1
        ; sub1
        ; fvars_1 = List.tl state.fvars_1
        }
      , invert )

let right_step state ?(invert = false) ?(binder = None) t2 sub2 =
  match (binder : Context.entry option) with
  | None ->
      ({ state with choices = Side Right :: state.choices; t2; sub2 }, invert)
  | Some { binder; type_ } ->
      let fvar = List.hd state.fvars_2 in
      let context = Context.add fvar binder type_ state.context in
      let choice =
        Binder (Right, Option.get @@ Unif.get_sitem state.subst fvar)
      in
      ( { state with
          choices = choice :: state.choices
        ; context
        ; t2 = Term.instantiate fvar t2
        ; sub2
        ; fvars_2 = List.tl state.fvars_2
        }
      , invert )

(** [instantiable state fvar] checks whether [fvar]
    is bound to some term [witness] in [state.subst], and checks if [witness] 
    has all its free variables in scope (which means we are allowed to instantiate
    the corresponding quantifier). *)
let instantiable state fvar : bool =
  match Unif.get_sitem state.subst fvar with
  | Some (SBound witness) ->
      List.for_all (fun v -> Context.mem v state.context)
      @@ Term.free_vars witness
  | _ -> false

let head_instantiable state side =
  match side with
  | Left -> begin
      match state.fvars_1 with
      | fvar :: _ when instantiable state fvar -> true
      | _ -> false
    end
  | Right -> begin
      match state.fvars_2 with
      | fvar :: _ when instantiable state fvar -> true
      | _ -> false
    end

let is_bound subst fvar =
  match Unif.get_sitem subst fvar with Some (SBound _) -> true | _ -> false

let head_not_bound state side =
  match side with
  | Left -> begin
      match state.fvars_1 with
      | fvar :: _ when not @@ is_bound state.subst fvar -> true
      | _ -> false
    end
  | Right -> begin
      match state.fvars_2 with
      | fvar :: _ when not @@ is_bound state.subst fvar -> true
      | _ -> false
    end

(** Perform a single backwards step.
    This returns the updated state and a flag indicating whether we should invert the polarity. *)
let backward_step (state : state) : state * bool =
  let fo1 = FirstOrder.view state.env state.context state.t1 in
  let fo2 = FirstOrder.view state.env state.context state.t2 in

  (* It is very important that we try the invertible rules before the other rules. *)
  match ((fo1, state.sub1), (fo2, state.sub2)) with
  (***********************************************************************)
  (* Right INVERTIBLE rules. *)
  (***********************************************************************)
  (* Rule R¬ *)
  | _, (FConn (Not, [ f0 ]), 1 :: sub) -> right_step state ~invert:true f0 sub
  (* Rule R⇒₁ *)
  | _, (FImpl (f0, f1), 0 :: sub) -> right_step state ~invert:true f0 sub
  (* Rule R⇒₂ *)
  | _, (FImpl (f0, f1), 1 :: sub) -> right_step state f1 sub
  (* Rule R⇔₁ *)
  | _, (FConn (Equiv, [ f1; f2 ]), 1 :: sub) -> failwith "backward_step: todo"
  (* Rule R⇔₂ *)
  | _, (FConn (Equiv, [ f1; f2 ]), 2 :: sub) -> failwith "backward_step: todo"
  (* Rule R∀s *)
  | _, (FBind (Forall, x, ty, f1), 1 :: sub) when head_not_bound state Right ->
      right_step state ~binder:(Some { binder = x; type_ = ty }) f1 sub
  (***********************************************************************)
  (* Left INVERTIBLE rules. *)
  (***********************************************************************)
  (* Rule L∨₁ *)
  | (FConn (Or, [ f1; f2 ]), 1 :: sub), _ -> left_step state f1 sub
  (* Rule L∨₂ *)
  | (FConn (Or, [ f1; f2 ]), 2 :: sub), _ -> left_step state f2 sub
  (* Rule L∃s *)
  | (FBind (Exist, x, ty, f1), 2 :: 1 :: sub), _ when head_not_bound state Left
    ->
      left_step state ~binder:(Some { binder = x; type_ = ty }) f1 sub
  (***********************************************************************)
  (* Right rules. *)
  (***********************************************************************)
  (* Rules R∧₁ and R∨₁ *)
  | _, (FConn (conn, [ f1; f2 ]), 1 :: sub) when conn = And || conn = Or ->
      right_step state f1 sub
  (* Rules R∧₂ and R∨₂ *)
  | _, (FConn (conn, [ f1; f2 ]), 2 :: sub) when conn = And || conn = Or ->
      right_step state f2 sub
  (* Rules R∃s and R∃i *)
  | _, (FBind (Exist, x, ty, f1), 2 :: 1 :: sub)
    when head_not_bound state Right || head_instantiable state Right ->
      right_step state ~binder:(Some { binder = x; type_ = ty }) f1 sub
  (***********************************************************************)
  (* Left rules. *)
  (***********************************************************************)
  (* Rule L⇒₂ *)
  | (FImpl (f0, f1), 1 :: sub), _ -> left_step state f1 sub
  (* Rules L∧₁ and Rule L⇔₁ *)
  | (FConn (conn, [ f1; f2 ]), 1 :: sub), _ when conn = And || conn = Equiv ->
      left_step state f1 sub
  (* Rules L∧₂ and L⇔₂ *)
  | (FConn (conn, [ f1; f2 ]), 2 :: sub), _ when conn = And || conn = Equiv ->
      left_step state f2 sub
  (* Rule L∀s and L∀i *)
  | (FBind (Forall, x, ty, f1), 1 :: sub), _
    when head_not_bound state Left || head_instantiable state Left ->
      left_step state ~binder:(Some { binder = x; type_ = ty }) f1 sub
  (* No applicable rule. *)
  | _ -> failwith "Interact.backward_step : no rule is applicable."

(** Perform a single forward step.
    This returns the updated state and a flag indicating whether we should invert the polarity. *)
let forward_step (state : state) : state * bool =
  let fo1 = FirstOrder.view state.env state.context state.t1 in
  let fo2 = FirstOrder.view state.env state.context state.t2 in

  (* It is very important that we try the invertible rules before the other rules. *)
  match ((fo1, state.sub1), (fo2, state.sub2)) with
  (***********************************************************************)
  (* INVERTIBLE rules. *)
  (***********************************************************************)
  (* Rule F∃s *)
  | _, (FBind (Exist, x, ty, f1), 2 :: 1 :: sub) when head_not_bound state Right
    ->
      right_step state ~binder:(Some { binder = x; type_ = ty }) f1 sub
  | (FBind (Exist, x, ty, f1), 2 :: 1 :: sub), _ when head_not_bound state Left
    ->
      left_step state ~binder:(Some { binder = x; type_ = ty }) f1 sub
  (***********************************************************************)
  (* Non invertible rules. *)
  (***********************************************************************)
  (* Rules F∧₁ and F∨₁ and F⇔₁ *)
  | _, (FConn (conn, [ f1; f2 ]), 1 :: sub)
    when conn = And || conn = Or || conn = Equiv ->
      right_step state f1 sub
  | (FConn (conn, [ f1; f2 ]), 1 :: sub), _
    when conn = And || conn = Or || conn = Equiv ->
      left_step state f1 sub
  (* Rules F∧₂ and F∨₂ and F⇔₂ *)
  | _, (FConn (conn, [ f1; f2 ]), 2 :: sub)
    when conn = And || conn = Or || conn = Equiv ->
      right_step state f2 sub
  | (FConn (conn, [ f1; f2 ]), 2 :: sub), _
    when conn = And || conn = Or || conn = Equiv ->
      left_step state f2 sub
  (* Rule F⇒₁ *)
  | _, (FImpl (f0, f1), 0 :: sub) -> right_step state ~invert:true f0 sub
  | (FImpl (f0, f1), 0 :: sub), _ -> left_step state ~invert:true f0 sub
  (* Rule F⇒₂ *)
  | _, (FImpl (f0, f1), 1 :: sub) -> right_step state f1 sub
  | (FImpl (f0, f1), 1 :: sub), _ -> left_step state f1 sub
  (* Rule F¬ *)
  | _, (FConn (Not, [ f0 ]), 1 :: sub) -> right_step state ~invert:true f0 sub
  | (FConn (Not, [ f0 ]), 1 :: sub), _ -> left_step state ~invert:true f0 sub
  (* Rules F∀s and F∀i *)
  | _, (FBind (Forall, x, ty, f1), 1 :: sub)
    when head_not_bound state Right || head_instantiable state Right ->
      right_step state ~binder:(Some { binder = x; type_ = ty }) f1 sub
  | (FBind (Forall, x, ty, f1), 1 :: sub), _
    when head_not_bound state Left || head_instantiable state Left ->
      left_step state ~binder:(Some { binder = x; type_ = ty }) f1 sub
  (* No applicable rule. *)
  | _ -> failwith "Interact.forward_step : no rule is applicable."

type dnd_mode = Forward | Backward

let invert_mode = function Forward -> Backward | Backward -> Forward

(** Print some debug information about the state. *)
let dump_state ?(verbose = false) state mode : unit =
  let pp_term t =
    Notation.term_to_string state.env ~ctx:state.context
    @@ Unif.apply state.subst t
  in
  let pp_var v =
    let term = Unif.apply state.subst @@ Term.mkFVar v in
    Format.sprintf "%s --> %s" (FVarId.show v) (Term.show term)
  in

  if verbose
  then begin
    Log.str "------------------";

    (* Print the raw linkage. *)
    Log.printf "RAW t1 : %s" @@ Term.show state.t1;
    Log.printf "RAW t2 : %s" @@ Term.show state.t2;

    (* Print the subs. *)
    Log.printf "sub1 : %s" @@ List.to_string string_of_int state.sub1;
    Log.printf "sub2 : %s" @@ List.to_string string_of_int state.sub2;

    (* Print the raw substitution on the remaining free variables. *)
    Log.printf "RAW fvars_1 : %s"
    @@ List.to_string ~sep:" | " pp_var state.fvars_1;
    Log.printf "RAW fvars_2 : %s"
    @@ List.to_string ~sep:" | " pp_var state.fvars_2
  end;

  (* Print the pretty linkage. *)
  Log.printf "%s %s %s" (pp_term state.t1)
    (match mode with Forward -> "*" | Backward -> "|-")
    (pp_term state.t2)

(** Print the most recent choice that was added to the itrace. *)
let dump_last_choice state : unit =
  let choice = List.hd state.choices in
  let pp_side = function Left -> "[left]" | Right -> "[right]" in
  match choice with
  | Side side -> Log.printf ">>> side %s" (pp_side side)
  | Binder (side, SRigid) | Binder (side, SFlex) ->
      Log.printf ">>> binder %s" (pp_side side)
  | Binder (side, SBound witness) ->
      Log.printf ">>> binder %s instantiate [%s]" (pp_side side)
        (Notation.term_to_string state.env ~ctx:state.context
        @@ Unif.apply state.subst witness)

(** The main interaction loop. *)
let rec interact (state : state) mode : choice list =
  (* Print some debug info. *)
  dump_state state mode;

  (* For the L= rules, we put the rewrite direction
     (Left for left-to-right, Right for right-to-left) at the end
     of the choice list. *)
  match ((state.t1, state.sub1), (state.t2, state.sub2)) with
  (* Rule id *)
  | (_, []), (_, []) -> List.rev state.choices
  (* Rule L=₁ *)
  | (App (_, Cst eq, _), [ 2 ]), _ when Name.equal eq Constants.eq ->
      List.rev (Side Left :: state.choices)
  | (App (_, Cst eq, _), [ 3 ]), _ when Name.equal eq Constants.eq ->
      List.rev (Side Right :: state.choices)
  (* Rule L=₂ *)
  | _, (App (_, Cst eq, _), [ 2 ]) when Name.equal eq Constants.eq ->
      List.rev (Side Left :: state.choices)
  | _, (App (_, Cst eq, _), [ 3 ]) when Name.equal eq Constants.eq ->
      List.rev (Side Right :: state.choices)
  (* All other rules. *)
  | _ ->
      (* Perform one interaction step. *)
      let state, invert =
        match mode with
        | Forward -> forward_step state
        | Backward -> backward_step state
      in
      (* Print some debug info. *)
      dump_last_choice state;
      (* Decide on the next interaction mode. *)
      let mode = if invert then invert_mode mode else mode in
      (* Continue. *)
      interact state mode

(** Swap the roles of [t1] and [t2] in the state. *)
let swap_sides state : state =
  { t1 = state.t2
  ; sub1 = state.sub2
  ; fvars_1 = state.fvars_2
  ; t2 = state.t1
  ; sub2 = state.sub1
  ; fvars_2 = state.fvars_1
  ; choices =
      List.map
        (function
          | Side side -> Side (opp_side side)
          | Binder (side, sitem) -> Binder (opp_side side, sitem))
        state.choices
  ; env = state.env
  ; context = state.context
  ; subst = state.subst
  }

let item_of_path (path : Path.t) (pregoal : Logic.pregoal) : Logic.item =
  match path.kind with
  | Concl -> Concl pregoal.g_concl
  | Hyp name ->
      let hyp = Logic.Hyps.by_name pregoal.g_hyps name in
      Hyp (name, hyp)
  | VarHead _ | VarType _ | VarBody _ ->
      failwith "Interact.dlink : invalid link (a path points to a variable)."

let dlink ((src, src_fvars) : Path.t * FVarId.t list)
    ((dst, dst_fvars) : Path.t * FVarId.t list) subst pregoal : itrace =
  (* Destruct the link. *)
  assert (src.goal = dst.goal);
  let env = pregoal.g_env in
  let src_term = term_of_item @@ item_of_path src pregoal in
  let dst_term = term_of_item @@ item_of_path dst pregoal in

  (* Build the initial state. *)
  let state =
    { env
    ; context = Context.empty
    ; t1 = src_term
    ; t2 = dst_term
    ; sub1 = src.sub
    ; sub2 = dst.sub
    ; fvars_1 = src_fvars
    ; fvars_2 = dst_fvars
    ; subst
    ; choices = []
    }
  in

  (* Compute the interaction. *)
  let choices =
    match (src.kind, dst.kind) with
    | Hyp _, Concl -> interact state Backward
    | Concl, Hyp _ -> interact (swap_sides state) Backward
    | Hyp _, Hyp _ -> interact state Forward
    | _ -> failwith "Interact.dlink : invalid link."
  in
  (choices, src_fvars, dst_fvars)
