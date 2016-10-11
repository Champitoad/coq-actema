open Formula

type goal = {
  hypothesis : formula list;
  conclusion : formula;
}

let make_goal hypothesis conclusion =
  { hypothesis; conclusion }

type dgoal =
  | ClearHypothesis of Id.t
  | PushHypothesis of formula

let change goal dgoal =
  match dgoal with
    | ClearHypothesis id ->
      let hypothesis =
	List.filter (fun f -> f.identifier <> id) goal.hypothesis
      in
      { goal with hypothesis }
    | PushHypothesis f ->
      { goal with hypothesis = f :: goal.hypothesis }

