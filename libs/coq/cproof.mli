
module State : sig
  type t
end

val new_proof : EConstr.t -> State.t

val id_proof : unit -> State.t

val get_goals : State.t -> Pp.t list

val parse_tactic : State.t -> string -> unit Proofview.tactic option

val send_tactic : State.t -> unit Proofview.tactic -> State.t

val refine_tactic : State.t -> EConstr.t -> unit Proofview.tactic
