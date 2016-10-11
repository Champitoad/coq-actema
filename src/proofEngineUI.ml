(** Interpret the user action in terms of tactics. *)
let tactic_of_user_action goal = function
  | UI.Use id ->
    ProofEngine.assumption id
  | UI.Transform id ->
    match ProofEngine.lookup_term goal id with
      | Formula.Conj _ ->
	ProofEngine.split id
      | _ ->
	ProofEngine.assumption id

