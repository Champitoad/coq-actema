val actema_tac : string -> unit Proofview.tactic
val actema_force_tac : string -> unit Proofview.tactic
val calltac_tac : string -> EConstr.constr list -> unit Proofview.tactic
val test_tac : unit Proofview.tactic