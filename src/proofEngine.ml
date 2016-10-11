open Formula
open Goals
open Goal

exception TacticFailed

type tactic = goal -> dgoals

let lookup_hypothesis goal id =
  List.find (fun f -> f.identifier = id) goal.hypothesis

let is_conclusion goal id =
  goal.conclusion.identifier = id

let lookup goal id =
  try
    lookup_hypothesis goal id
  with Not_found ->
    if is_conclusion goal id then
      goal.conclusion
    else
      raise Not_found

let lookup_term goal id =
  (lookup goal id).term

let assumption : Id.t -> tactic =
  fun id goal ->
    try
      if Formula.equivalent (lookup_hypothesis goal id) goal.conclusion then
	PopGoal goal
      else
	raise TacticFailed
    with Not_found ->
      raise TacticFailed

let split : Id.t -> tactic =
  fun id goal ->
    try
      let subformulas =
	match lookup_term goal id with
	  | Conj ts -> ts
	  | x -> [x]
      in
      if is_conclusion goal id then
	Compose (
	  PopGoal goal
	  :: List.map (fun f -> PushGoal { goal with conclusion = Formula.mk f }) subformulas
	)
      else
	Compose (
	  OnCurrent (ClearHypothesis id)
	  :: List.map (fun f -> OnCurrent (PushHypothesis (Formula.mk f))) subformulas
	)
    with Not_found ->
      raise TacticFailed

type proof_state = goal list

let rec change proof_state dgoals =
  match proof_state, dgoals with
    | _, PushGoal g' ->
      g' :: proof_state
    | g :: gs, PopGoal g' ->
      assert (g = g'); gs
    | _, Identity ->
      proof_state
    | _, Compose dgoalss ->
      List.fold_left change proof_state dgoalss
    | g :: gs, OnCurrent dgoal ->
      (Goal.change g dgoal) :: gs
    | _, _ ->
      assert false

exception NoGoal
let current_goal = function
  | [] -> raise NoGoal
  | g :: _ -> g

let apply proof_state tactic =
  match proof_state with
    | [] -> raise NoGoal
    | g :: _ -> tactic g

let start_proof_for (goal : goal) : proof_state =
  [goal]

let qed proof_state =
  proof_state = []
