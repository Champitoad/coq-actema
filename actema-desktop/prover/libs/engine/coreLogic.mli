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

val form_of_item : item -> form
val expr_of_item : ?where:[< `Body | `Head > `Body ] -> item -> expr
val term_of_item : ?where:[< `Body | `Head > `Body ] -> item -> term
val ipath_of_path : path -> ipath
val path_of_ipath : ipath -> path
val destr_ipath : Proof.proof -> ipath -> Proof.goal * item * (Utils.uid list * term)

val mk_ipath : ?ctxt : ctxt -> ?sub:int list -> int -> ipath
val item_ipath : ipath -> ipath
val concl_ipath : Proof.goal -> ipath


val goal_of_ipath : Proof.proof -> ipath -> Proof.goal
val gid_of_ipath : Proof.proof -> ipath -> Handle.t 
val term_of_ipath : Proof.proof -> ipath -> term
val env_of_ipath : Proof.proof -> ipath -> env
val is_sub_path : ipath -> ipath -> bool


val add_local_def : string * Fo.type_ * Fo.expr -> tactic
val generalize : Handle.t -> tactic
val move : Handle.t -> Handle.t option -> tactic
val ivariants : targ -> string list
val evariants : targ -> Handle.t -> string list

(** [opp p] returns the opposite polarity of [p] *)
val opp : pol -> pol

(** [direct_subform_pol (p, f) i] returns the [i]th direct subformula of [f]
      together with its polarity, given that [f]'s polarity is [p] *)
val direct_subform_pol : pol * form -> int -> pol * form

val direct_subterm_pol : pol * term -> int -> pol * term

(** [subform_pol (p, f) sub] returns the subformula of [f] at path [sub] together
      with its polarity, given that [f]'s polarity is [p] *)
val subform_pol : pol * form -> int list -> pol * Fo.form

(** [neg_count f sub] counts the number of negations in [f] along path [sub] *)
val neg_count : form -> int list -> int

(** [pol_of_item it] returns the polarity of the item [it] *)
val pol_of_item : item -> pol

(** [pol_of_ipath proof p] returns the polarity of the subformula
    at path [p] in [proof] *)
val pol_of_ipath : Proof.proof -> ipath -> pol

val direct_subterm : term -> int -> term
val subterm : term -> int list -> term
val modify_direct_subterm : (term -> term) -> term -> int -> term

val modify_subterm :
  ('a -> term -> term) -> (int -> term -> 'a -> 'a) -> 'a -> term -> int list -> term

(*********************************************************************************)
type choice = int * (LEnv.lenv * LEnv.lenv * expr) option
type itrace = choice list

val dlink : link -> Form.Subst.subst * Form.Subst.subst -> Proof.proof -> Proof.subgoal * itrace
