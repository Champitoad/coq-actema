(** This module implements translations between Coq terms and Actema terms. *)

open Utils.Pervasive
open Api
open CoqUtils
open Lang
module Bimap = Utils.Bimap

(** Translating from Coq to Actema. *)
module Export : sig
  (* We can't translate the following term. *)
  exception CannotTranslate of EConstr.t

  (** Translate a Coq term to an Actema term. 
      Also returns the environment needed to type the term. *)
  val econstr : Goal.t -> EConstr.t -> Term.t * Env.t

  (** Translate a Coq goal to an Actema goal. This includes : 
    - Translating the conclusion. 
    - Translating the hypotheses and variables. 
    - Building the environment needed to type the goal. *)
  val goal : Goal.t -> Logic.pregoal

  (** Translate all the lemmas we can to Actema, along with 
      the environment needed to type them. *)
  val lemmas : Goal.t -> Logic.lemma list * Env.t
end

(** When translating Coq terms to Actema terms, we loose the distinction 
    between related but different Coq names, i.e. we translate everything to [Term.Cst]. 
    Symbols allows us to remember the correspondance between Actema names and Coq names. *)
module Symbols : sig
  type symbol =
    (* Constant symbol. *)
    | SCst of Names.Constant.t
    (* Constructor symbol. *)
    | SCtr of Names.Construct.t
    (* Inductive symbol. *)
    | SInd of Names.Ind.t
    (* Local variable (from Coq's local context). *)
    | SVar of Names.Id.t

  (** A symbol table is a (bi-directional) mapping between symbols and Actema names.
      Symbol tables are used only in the plugin (not in the prover). *)
  module Table : Bimap.S with type key = Name.t and type value = symbol

  (** Extract all the symbols corresponding to global constants, 
      inductives and constructors registered in Coq's environment. *)
  val globals : Goal.t -> Table.t

  (** Extract all the symbols corresponding to local variables in a Coq goal. *)
  val locals : Goal.t -> Table.t

  (** Extract both local and global symbols. *)
  val all : Goal.t -> Table.t

  (** Translate a symbol to a Coq [EConstr.t], using fresh universe instances. *)
  val to_econstr : Goal.t -> symbol -> EConstr.t
end

(** Translating from Actema to Coq. *)
module Import : sig
  (** Translate an Actema term into a Coq term. 
      This requires a symbol table (as produced e.g. by [Symbols.all]) 
      to map Actema names to Coq constants. *)
  val term : Goal.t -> Symbols.Table.t -> Term.t -> EConstr.t
end
