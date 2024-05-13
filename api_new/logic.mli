(***************************************************************************************)
(** Handles *)

(** A handle is used to uniquely identify a hypothesis. *)
(*module Handle : sig
    include Map.OrderedType

    val pp : Format.formatter -> t -> unit
    val show : t -> string
    val ofint : int -> t
    val fresh : unit -> t
    val eq : t -> t -> bool
    val toint : t -> int
  end

  (***************************************************************************************)
  (** Items *)

  (** A single hypothesis. *)
  type hyp = { h_src : Handle.t option; h_gen : int; h_form : Term.t } [@@deriving show]

  (** A module to handle collections of hypotheses. *)
  module Hyps : sig
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

  (** A single lemma. *)
  type lemma = { l_full : Name.t; l_user : string; l_form : Term.t } [@@deriving show]

    (** A module to handle a collection of lemmas together with an environment to type the lemmas.  *)
    module Lemmas : sig
      type t

      val empty : t
      val extend_env : Fo.env -> t -> t
      val env : t -> Fo.env
      val byid : t -> Handle.t -> lemma
      val add : t -> Handle.t -> lemma -> t
      val remove : t -> Handle.t -> t
      val ids : t -> Handle.t list
      val map : (lemma -> lemma) -> t -> t
      val iter : (lemma -> unit) -> t -> unit
      val filter : (lemma -> bool) -> t -> t
      val to_list : t -> (Handle.t * lemma) list
      val of_list : (Handle.t * lemma) list -> t
    end
  (** A single pregoal. *)
  type pregoal = { g_env : Env.t; g_hyps : hyp list; g_goal : Term.t }

  type goal = { g_id : Handle.t; g_pregoal : pregoal }
  type subgoal = (Handle.t option * form list) list * form

  (** An item in a goal. *)
  type item =
    | Concl of Term.t  (** Conclusion. *)
    | Hyp of Handle.t * hyp  (** Hypothesis. *)
    | Var of Name.t * bvar  (** Variable. *)
  [@@deriving show]

  (***************************************************************************************)
  (** Paths *)

  (** This module defines paths to items.
      A path can point to :
      - A subterm of the conclusion.
      - A subterm of a hypothesis.
      - A variable definition : either to the head (variable name) or a subterm of the definition's body.
      A path points to an item in a specific goal. *)
  module Path : sig
    (** What kind of object does a path point to ? *)
    type kind = [ `Hyp | `Concl | `Var of [ `Head | `Body ] ] [@@deriving show]

    (** What object does a path point to ?
        Depending on the [kind], the [handle] is :
        - For [`Concl], it is always [0].
        - For [`Hyp], it is the index of the corresponding hypothesis in the goal.
        - For [`Var], it is the index of the corresponding variable binding in the goal's environment. *)
    type ctxt = { kind : pkind; handle : int } [@@deriving show]

    (** A path to a subterm of an item.
        As an example, consider the goal :
          [x := 4, y := 3 * x + 2, x + 3 * y = 0 |- x = 0]
        Assuming this is the goal with index 0, possible paths include :
        - [{ root = 0 ; ctxt = { kind = `Concl ; handle = 0 } ; sub = [0] }]
          which points to the variable [x] in the conclusion.
        - [{ root = 0 ; ctxt = { kind = `Var `Body ; handle = 1 } ; sub = [0] }]
          which points to the expression [3 * x] in the definition of [y].
        - [{ root = 0 ; ctxt = { kind = `Var `Head ; handle = 0 } ; sub = [] }]
          which points to the variable name [x] in the definition of [x].
    *)
    type t =
      { root : int  (** The index of the goal we point to. *)
      ; ctxt : ctxt  (** The object we point to. *)
      ; sub : int list  (** The position in the term we point to. *)
      }
    [@@deriving show]

    (** The [string] argument contains the path (encoded as text). *)
    exception InvalidPath of string

    (** Create a new path. *)
    val make : ?ctxt:ctxt -> ?sub:int list -> int -> t

    (** Destruct a path, i.e. get all the information relevant to a path. *)
    val destr : Proof.proof -> t -> Proof.goal * item * (Utils.uid list * term)

    (** Decode a path encoded as a string. *)
    val of_string : string -> t

    (** Encode a path to a string. *)
    val to_string : t -> string

    (** [IPath.subpath p1 p2] checks whether [p1] is a subpath of [p2]. *)
    val subpath : t -> t -> bool

    (** Set the [sub] parts of a path to the empty list. *)
    val erase_sub : t -> t

    (** Make a path to the (root of the) conclusion of a goal. *)
    val to_concl : Proof.goal -> t

    (** Return the goal that contains the path. *)
    val goal : Proof.proof -> t -> Proof.goal

    (** Return the identifer of the goal that contains the path. *)
    val gid : Proof.proof -> t -> Handle.t

    (** Return the subterm pointed at by the path. *)
    val term : Proof.proof -> t -> term

    (** Given that the path points to a subterm [t], return the environment that is valid at [t]
        (i.e. contains local variables bound by quantifiers above [t]). *)
    val env : Proof.proof -> t -> env
  end*)
