open CoreLogic
open Fo

type link = IPath.t * IPath.t
type hyperlink = IPath.t list * IPath.t list

type asource = { kind : asource_kind; selection : selection }
and asource_kind = [ `Click of IPath.t | `DnD of adnd | `Ctxt ]
and adnd = { source : IPath.t; destination : IPath.t option }
and selection = IPath.t list

type osource = [ `Click of IPath.t | `DnD of link | `Ctxt ]

type linkaction =
  [ `Nothing
  | `Both of linkaction * linkaction
  | `Subform of Form.Subst.subst * Form.Subst.subst
  | `Instantiate of expr * IPath.t
  | `Rewrite of expr * expr * IPath.t list
  | `Fold of vname * IPath.t list
  | `Unfold of vname * IPath.t list ]

type action_type =
  [ `Intro of int
  | `Elim of Handle.t * int
  | `Lemma of name
  | `Ind of Handle.t
  | `Simpl of IPath.t
  | `Red of IPath.t
  | `Indt of IPath.t
  | `Case of IPath.t
  | `Pbp of IPath.t
  | `Fold of vname
  | `Unfold of vname
  | `Hyperlink of hyperlink * linkaction list ]

type action = Handle.t * action_type

type aoutput =
  { description : string
  ; icon : string option
  ; highlights : IPath.t list
  ; kind : osource
  ; action : action
  }

val hyperlink_of_link : link -> hyperlink

(** Get the list of all valid actions on a given proof state. *)
val actions : Proof.proof -> asource -> aoutput list

(** The type of hyperlink predicates [hlpred] captures functions which
    map a hyperlink in a proof to a list of possible link actions.

    One can emulate a traditional boolean predicate by returning the singleton
    [`Nothing] to indicate membership, or the empty list to indicate absence
    thereof. *)

type lpred = Proof.proof -> link -> linkaction list
type hlpred = Proof.proof -> hyperlink -> linkaction list

val hlpred_of_lpred : lpred -> hlpred

(** [hlpred_mult lps] returns a hyperlink predicate that denotes the cartesian
         product of the actions denoted by the hyperlink predicates in [lps]. *)
val hlpred_mult : hlpred list -> hlpred

(** [hlpred_add lps] returns a hyperlink predicate that denotes the disjoint
         union of the actions denoted by the hyperlink predicates in [lps]. *)
val hlpred_add : hlpred list -> hlpred

(** [hlpred_if_empty p1 p2] is equivalent to [p1] at links where the
         latter is non-empty, and [p2] elsewhere. *)
val hlpred_if_empty : hlpred -> hlpred -> hlpred

(** [search_linkactions hlp proof (src, dst)] returns all links between
    subterms of [src] and [dst] in [proof] that can interact according to
    the hyperlink predicate [hlp], together with the lists of possible link
    actions determined by the predicate.
   
    If [fixed_srcs] (resp. [fixed_dsts]) is set, the function returns only
    hyperlinks with sources [fixed_srcs] (resp. destinations [fixed_dsts]),
    and whose destinations (resp. sources) are subterms of [dst] (resp.
    [src]). *)
val search_linkactions :
     ?fixed_srcs:IPath.t list
  -> ?fixed_dsts:IPath.t list
  -> hlpred
  -> Proof.proof
  -> link
  -> (hyperlink * linkaction list) list

(** [wf_subform_link proof (src, dst)] checks if [src] and [dst] lead to
    unifiable subformulas of opposite polarities in the focused goal of
    [proof], and returns the associated substitutions if they do inside a
    [`Subform] link action.
             
    If [drewrite] is set to [true], it only checks for deep rewrite links,
    that is links where one side is a negative equality operand, and the other
    side an arbitrary unifiable subexpression of the same type. *)
val wf_subform_link : ?drewrite:bool -> lpred

(** [intuitionistic_link lnk] checks if [lnk] is an intuitionistic link,
                   and returns a [`Nothing] link action if so. *)
val intuitionistic_link : lpred

(** [instantiate_link proof (srcs, dsts)] checks if [srcs] (resp.
    [dsts]) leads to an expression, and [dsts] (resp. [srcs]) leads either to
    an instantiable quantified subformula, or the set of occurrences of an
    instantiable quantified variable. It it succeeds, it returns the
    corresponding [`Instantiate] link action. *)
val instantiate_link : hlpred

(** [rewrite_link lnk] checks if [lnk] is a rewrite hyperlink. That is, one
    end of the link is the left or right-hand side expression [e] of an
    equality hypothesis, and the other end a non-empty set of arbitrary
    subterms where all occurrences of [e] are to be rewritten.
             
    If the check succeeds, it returns a [`Rewrite (red, res, tgts)] link
    action, where [red] and [res] are respectively the reduced ([e]) and
    residual expressions, and [tgts] are the targeted subterms. *)
val rewrite_link : hlpred

(** [fold_link lnk] checks if [lnk] is a fold hyperlink. That is, one
    end of the link is the head [x] (resp. body [e]) of a local variable
    definition, and the other end a non-empty set of arbitrary subterms where
    all occurrences of [x] (resp. [e]) are to be rewritten into [e] (resp.
    [x]).
             
    If the check succeeds, it returns either a [`Fold] or [`Unfold] link action. *)
val fold_link : hlpred

(**************************************************************)

(** Filter the lemma database by keeping only the lemmas that have a dnd interaction with a given selection. 
    This only changes the lemma database. *)
val filter_db_by_selection : IPath.t -> Proof.proof -> Proof.proof

(** Filter the lemma database by keeping only the lemmas whose name matches a given pattern.
        This only changes the lemma database.  *)
val filter_db_by_name : string -> Proof.proof -> Proof.proof
