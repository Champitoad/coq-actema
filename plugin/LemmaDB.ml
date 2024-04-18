open Api
open Proofview
open CoqUtils
open Translate

(** Export all the lemmas we can translate to actema, 
    along with their environment. *)
let export_lemmas () : (Logic.lemma list * Logic.env) tactic =
  let open PVMonad in
  let* coq_goals_tacs = Goal.goals in
  let* lemmas, sign =
    Stdlib.List.fold_right
      begin
        fun coq_goal_tac acc ->
          let* coq_goal = coq_goal_tac in
          let* lemmas, sign = acc in
          let new_lemmas, new_sign = Export.lemmas coq_goal sign in
          return (new_lemmas @ lemmas, new_sign)
      end
      coq_goals_tacs
      (return ([], peano))
  in
  let env = Export.env_of_varsign (NameMap.empty, sign) in
  return (lemmas, env)

let preselect_lemmas_name pattern lemmas =
  let filter lem =
    (* Check that the pattern is an exact substring of the lemma's name.
       The test is case-insensitive. *)
    let user_name = String.lowercase_ascii lem.Logic.l_user in
    let pattern = String.lowercase_ascii pattern in
    try
      ignore (BatString.find user_name pattern);
      true
    with Not_found -> false
  in
  List.filter filter lemmas

let preselect_lemmas_selection selection lemmas = lemmas
