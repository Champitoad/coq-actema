open Fo

exception TacticNotApplicable
exception InvalidPath of string
exception InvalidSubFormPath of int list
exception InvalidSubExprPath of int list

type targ = Proof.proof * Handle.t
type tactic = targ -> Proof.proof
type path = string
type pkind = [ `Hyp | `Concl | `Var of [ `Head | `Body ] ]
type ctxt = { kind : pkind; handle : int }
type ipath = { root : int; ctxt : ctxt; sub : int list }
type link = ipath * ipath
type hyperlink = ipath list * ipath list

type item =
  [ `C of form  (** Conslusion. *)
  | `H of Handle.t * Proof.hyp  (** Hypothesis. *)
  | `V of vname * bvar  (** Variable. *) ]

(** A polarity : positive, negative or superposed (i.e. both positive and negative). *)
type pol = Pos | Neg | Sup

val ipath_of_path : path -> ipath
val add_local_def : string * Fo.type_ * Fo.expr -> tactic
val generalize : Handle.t -> tactic
val move : Handle.t -> Handle.t option -> tactic
val ivariants : targ -> string list
val evariants : targ -> Handle.t -> string list

type asource = { kind : asource_kind; selection : selection }
and asource_kind = [ `Click of ipath | `DnD of adnd | `Ctxt ]
and adnd = { source : ipath; destination : ipath option }
and selection = ipath list

type osource = [ `Click of ipath | `DnD of link | `Ctxt ]

type linkaction =
  [ `Nothing
  | `Both of linkaction * linkaction
  | `Subform of Form.Subst.subst * Form.Subst.subst
  | `Instantiate of expr * ipath
  | `Rewrite of expr * expr * ipath list
  | `Fold of vname * ipath list
  | `Unfold of vname * ipath list ]

type action_type =
  [ `Intro of int
  | `Elim of Handle.t * int
  | `Ind of Handle.t
  | `Simpl of ipath
  | `Red of ipath
  | `Indt of ipath
  | `Case of ipath
  | `Pbp of ipath
  | `Fold of vname
  | `Unfold of vname
  | `Hyperlink of hyperlink * linkaction list ]

type action = Handle.t * action_type

type aoutput =
  { description : string
  ; icon : string option
  ; highlights : ipath list
  ; kind : osource
  ; action : action
  }

val path_of_ipath : ipath -> path

(** Get the list of all valid actions on a given proof state. *)
val actions : Proof.proof -> asource -> aoutput list

(** Filter the lemma database by keeping only the lemmas that have a dnd interaction with a given selection. 
    This only changes the lemma database. *)
val filter_db_by_selection : ipath -> Proof.proof -> Proof.proof

(** Filter the lemma database by keeping only the lemmas whose name matches a given pattern.
    This only changes the lemma database.  *)
val filter_db_by_name : string -> Proof.proof -> Proof.proof

module Translate : sig
  open Hidmap

  exception UnsupportedAction of action_type

  val export_action : hidmap -> Proof.proof -> action -> Api.Logic_t.action
end
