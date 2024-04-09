(* This module defines the core datastructure used in the prover : the proof state.
   The proof contains the list of active goals (along with their hypotheses, conclusion, environment)
   and some additional bookkeeping information. *)

open Fo

exception InvalidGoalId of Handle.t
exception InvalidHyphId of Handle.t
exception SubgoalNotOpened of Handle.t

(** Abstract type of a proof state. *)
type proof

(** A single hypothesis. *)
type hyp = { h_src : Handle.t option; h_gen : int; h_form : form }

(** A module to handle collections of hypotheses. *)
module Hyps : sig
  (** Abstract type of a collection of hypotheses. *)
  type t

  val empty : t
  val byid : t -> Handle.t -> hyp
  val add : t -> Handle.t -> hyp -> t
  val remove : t -> Handle.t -> t
  val move : t -> Handle.t -> Handle.t option -> t
  val bump : t -> t
  val ids : t -> Handle.t list
  val map : (hyp -> hyp) -> t -> t
  val iter : (hyp -> unit) -> t -> unit
  val to_list : t -> (Handle.t * hyp) list
  val of_list : (Handle.t * hyp) list -> t
end

type pregoal = { g_env : env; g_hyps : Hyps.t; g_goal : form }
type pregoals = pregoal list
type goal = { g_id : Handle.t; g_pregoal : pregoal }
type subgoal = (Handle.t option * form list) list * form

(** Metadata associated to a goal. *)
type meta = < > Js_of_ocaml.Js.t

val mk_hyp : ?src:Handle.t -> ?gen:int -> form -> hyp
val hidmap : proof -> Hidmap.hidmap

(** Create a fresh proof that contains a single goal. *)
val init : env -> form list -> form -> proof

(** Create a proof that contains several goals 
    and some potentially already existing data (in hidmap). *)
val ginit : Hidmap.hidmap -> pregoal list -> proof

(** Test whether the proof has some remaining active goals. *)
val closed : proof -> bool

(** Return a list of (the handles of) all active goals in the proof. *)
val opened : proof -> Handle.t list

(** Retrieve an active goal by its handle. *)
val byid : proof -> Handle.t -> pregoal

(** Get the lemma database. *)
val get_db : proof -> LemmaDB.t

(** Set the lemma database. *)
val set_db : proof -> LemmaDB.t -> proof

(** Attach metadata to a goal. *)
val set_meta : proof -> Handle.t -> meta option -> unit

(** Get the metadata attached to a goal. *)
val get_meta : proof -> Handle.t -> meta option

val sgprogress : pregoal -> ?clear:bool -> subgoal list -> pregoals

(** In a proof, replace a goal by a list of pregoals. 
    Returns the handles of the goals freshly created and the new proof state. *)
val xprogress : proof -> Handle.t -> pregoals -> Handle.t list * proof

(** A module to translate goals between API format (api/logic.atd) and Actema format (engine/fo.ml).
    See also CoreLogic.Translate. *)
module Translate : sig
  open Hidmap

  val import_goal : Api.Logic_t.goal -> pregoal * hidmap
  val export_goal : pregoal * hidmap -> Api.Logic_t.goal
end
