(** This module defines the language used by the frontend & prover. 
    We call this the Actema language to distinguish it from the language used by Coq.
    It is the which creates Actema terms (from Coq terms). *)

(***************************************************************************************)
(** Names *)

module Name : sig
  (** A name uniquely identifies a variable (local or global). It is essentially a
      wrapper around a string, but provides more efficient comparison functions by hashing 
      the string. Names are used pervasively in Actema so we provide an efficient and
      encapsulated implementation. *)
  type t

  (** Create a variable with the given name. This is a pure function. *)
  val make : string -> t

  (** Get the string representation of a variable. *)
  val show : t -> string

  (** Pretty-print a variable. *)
  val pp : Format.formatter -> t -> unit

  (** Compare variables efficiently. *)
  val compare : t -> t -> int

  (** Test for equality between variables efficiently. *)
  val equal : t -> t -> bool

  (** Get the hash of the name. This is O(1). *)
  val hash : t -> int

  (** A few modules on Names. *)

  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t
  module Hashtbl : Hashtbl.S with type key = t

  (** A dummy name. This is used when translating Coq terms 
      that cannot be represented in Actema. *)
  val dummy : t

  (** Coq's logical conjunction [and_ : Prop -> Prop -> Prop]. *)
  val and_ : t

  (** Coq's logical disjunction [or_ : Prop -> Prop -> Prop]. *)
  val or_ : t
end

(***************************************************************************************)
(** Terms *)

module Term : sig
  (** A grammar for a small dependently-typed language. 
      This is a private type : use the smart constructors provided below to build terms. *)
  type t = private
    (* [Var v] is a local variable bound by a lambda abstraction or a dependent product.
       It refers to the most recently bound variable with its name. *)
    | Var of Name.t
    (* [App f [x1; ...; xn]] represents the application [f x1 ... xn].
       We maintain the invariant that [f] itself is not an application,
       and that the argument list is not empty. *)
    | App of t * t list
    (* [Lambda x ty body] represents the lambda abstraction [fun x : ty => body].
       The term [ty] is the type of [x], and [x] can appear as a variable [Var x] in [body]. *)
    | Lambda of Name.t * t * t
    (* [Arrow A B] is the non-dependent product [A -> B], i.e. an arrow. *)
    | Arrow of t * t
    (* [Prod x A B] is the dependent product [forall x : A, B].
       [A] is the type of [x], and [x] can appear as a variable [Var x] in [body]. *)
    | Prod of Name.t * t * t
    (* [Cst c] is a global constant. Its type can be found in the environment.

       Examples of constants could be :
       - [nat] the inductive type of natural numbers.
       - [add] the addition on natural numbers.
       - [list] the inductive type of polymorphic lists.
       - [cons] the second constructor of [list].
       - [h] where h is a hypothesis (i.e. a variable of Coq's named context).

       Notable constants used in Actema (see names.mli for a list) :
       - Logical connectives [and], [or], etc.
       - The existential quantifier [ex].
    *)
    | Cst of Name.t
      (* We have two sorts : Prop and Type, with the following typing judgements :
         |- Prop : Type
         |- Type : Type

         Note that the Actema language cannot distinguish between universe levels :
         this means that some terms might unify in Actema but not in Coq.
         This is okay because Coq always checks we do the right thing. The alternative would
         be to work with a Type hierarchy in Actema, which seems like a painful effort
         for such little gain. *)
    | Sort of [ `Prop | `Type ]
  [@@deriving show]

  val mkVar : Name.t -> t

  (** Smart constructor for [Term.App], ensuring that the function is not an application. *)
  val mkApp : t -> t -> t

  (** Same as [mkApp] but with multiple arguments. 
      It also checks that the argument list is nonempty. *)
  val mkApps : t -> t list -> t

  val mkArrow : t -> t -> t

  (** [mkArrows [t1; ...; tn]] constructs the arrow [t1 -> ... -> tn]. 
      It assumes that the list is nonempty (i.e. n >= 1). *)
  val mkArrows : t list -> t

  val mkLambda : Name.t -> t -> t -> t
  val mkProd : Name.t -> t -> t -> t
  val mkCst : Name.t -> t
  val mkProp : t
  val mkType : t
  val mkSort : [ `Prop | `Type ] -> t
end

(***************************************************************************************)
(** Environments. *)

module Env : sig
  (** Some global variables require special formatting when pretty-printed. *)
  type pp_info =
    { symbol : string
          (** The symbol to use to print the constant. For instance we might want to 
              print [Coq.Init.Peano.plus] as [+]. By default we print a name [n] as [n]. *)
    ; position : [ `Prefix | `Infix | `Suffix ]
          (** The position of the constant with respect to its arguments.
              [`Infix] only makes sense for binary functions.
              [`Suffix] only makes sense for unary functions.
              [`Prefix] is always valid, and is what is used by default. *)
    }
  [@@deriving show]

  (** An environment contains all the information needed to :
      - Type check terms.
      - Pretty-print terms. *)
  type t =
    { constants : Term.t Name.Map.t
          (** The type of each constant, indexed by name. *)
    ; pp_info : pp_info Name.Map.t
          (** The information needed to pretty-print a constant, indexed by name. *)
    }

  (** The empty environment. *)
  val empty : t

  (** An environment containing a few constants. Used for testing.
      We assume that the types of the constants are well-typed. *)
  val test_env : t

  (** [Env.add_constant name ty env] adds the constant [name] with type [ty] 
      to the environment [env]. This does not add any pp information for [name]. *)
  val add_constant : Name.t -> Term.t -> t -> t
end

(***************************************************************************************)
(** Term utility functions. *)

module TermUtils : sig
  (** [subst name u t] replaces every free occurence of [Var name] by the term [u] 
      in the term [t]. *)
  val subst : Name.t -> Term.t -> Term.t -> Term.t

  (** [free_vars t] computes the set of free variables in [t]. *)
  val free_vars : Term.t -> Name.Set.t
end

(***************************************************************************************)
(** Typing. *)

module Typing : sig
  type typeError [@@deriving show]

  exception TypingError of typeError

  (** [check ?context env t] checks that [t] is well-typed, and returns the 
      type of [t] or raises a typing error. 
      The argument [context] gives the type of the free variables of [t] 
      (by default [context] is empty and [t] is assumed to be closed).
      
      If you already know [t] is well-typed use [typeof ?context env t] instead. *)
  val check : ?context:(Name.t * Term.t) list -> Env.t -> Term.t -> Term.t

  (** [typeof ?context env t] gets the type of the term [t]. 
      This assumes that [t] is well-typed, and is faster than [check env t]. *)
  val typeof : ?context:(Name.t * Term.t) list -> Env.t -> Term.t -> Term.t
end

(** This module defines functions for generating arbitrary terms. 
    These are used mainly for testing. 
    
    The algorithm to generate typed terms is inspired by : 
      Testing an Optimising Compiler by Generating Random Lambda Terms
      https://www.cse.chalmers.se/~russo/publications_files/AST2011.pdf *)
module TermGen : sig
  open QCheck2

  (** [simple ~closed env] generates arbitrary terms, not necessarily well-typed.
      The terms use only the constants defined in [env]. 
      The flag [closed] controls whether we allow terms with free variables or not. *)
  val simple : closed:bool -> Env.t -> Term.t Gen.t

  (** [typed ?context ?ty env] generates pairs [(term, ty)] where [term] has type 
      [ty] in environment [env]. 
      The terms use only the constants defined in [env]. 
      The argument [ty] is used to fix the type of the generated terms (by default it is
      chosen at random).
      The argument [context] defines which free variables we can use (by default [context]
      is empty i.e. we generate closed terms). *)
  val typed :
       ?context:(Name.t * Term.t) list
    -> ?ty:Term.t
    -> Env.t
    -> (Term.t * Term.t) Gen.t

  (** [context env] generates a typing context in [env]. 
      This can be fed to [typed] to generate open terms. *)
  val context : Env.t -> (Name.t * Term.t) list Gen.t
end
