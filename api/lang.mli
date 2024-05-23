(** This module defines the language used by the frontend & prover. 
    We call this the Actema language to distinguish it from the language used by Coq.
    It is the which creates Actema terms (from Coq terms). *)

open Utils

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

  (** We define the names of a few Coq constants that are handled in a special way. *)

  (** A dummy name. This is used when translating Coq terms 
      that cannot be represented in Actema. *)
  val dummy : t

  (** Coq's inductive [(=) : forall A : Type, A -> A -> Prop]. *)
  val eq : t

  (** Coq's inductive [nat : Type]. *)
  val nat : t

  (** Coq's inductive [list : Type -> Type]. *)
  val list : t

  (** Coq's logical conjunction [and_ : Prop -> Prop -> Prop]. *)
  val and_ : t

  (** Coq's logical disjunction [or_ : Prop -> Prop -> Prop]. *)
  val or_ : t

  (** Coq's logical negation [not : Prop -> Prop]. *)
  val not : t

  (** Coq's logical equivalence [equiv : Prop -> Prop -> Prop]. *)
  val equiv : t

  (** Coq's inductive [ex : forall A : Type, (A -> Prop) -> Prop]. *)
  val ex : t

  (** Coq's constructor [O : nat]. *)
  val zero : t

  (** Coq's constructor [S : nat -> nat]. *)
  val succ : t

  (** Coq's constant [add : nat -> nat -> nat]. *)
  val add : t

  (** Coq's constant [mul : nat -> nat -> nat]. *)
  val mul : t

  (** Coq's inductive [True : Prop]. *)
  val true_ : t

  (** Coq's inductive [False : Prop]. *)
  val false_ : t

  (** [is_logical_conn name] tests whether [name] corresponds to a logical connector. *)
  val is_logical_conn : t -> bool
end

(***************************************************************************************)
(** Terms *)

module Term : sig
  (** A grammar for a small dependently-typed language. 
      This is a private type : use the smart constructors provided below to build terms. *)
  type t = private
    (* [Var n] is a local variable bound by a lambda abstraction or a dependent product.
       The integer [n] is a de Bruijn index, starting at 0. *)
    | Var of int
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

  val mkVar : int -> t

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

(** [InvalidSubtermPath (t, sub)] indicates that the term [t] has no 
    subterm at path [sub]. *)
exception InvalidSubtermPath of Term.t * int list

(***************************************************************************************)
(** Typing contexts. *)

module Context : sig
  (** A typing context contains the name and type of the free variables in a term.
        Conceptually it is a stack of [(name, ty)], but may be implemented more efficiently. *)
  type t [@@deriving show]

  (** The empty typing context. *)
  val empty : t

  (** [size ctx] returns the number of bindings in [ctx]. *)
  val size : t -> int

  val to_list : t -> (Name.t * Term.t) list
  val of_list : (Name.t * Term.t) list -> t

  (** [push name ty ctx] adds the variable with name [name] and type [ty] to the context [ctx]. *)
  val push : Name.t -> Term.t -> t -> t

  (** [pop ctx] removes the most recent binding (i.e. at index 0) from [ctx]. *)
  val pop : t -> t option

  (** [get n ctx] returns the name and type of the n-th variable in [ctx]. *)
  val get : int -> t -> (Name.t * Term.t) option

  (** [get_by_type ty ctx] returns the list of all the variables that have type [ty] in [ctx]. *)
  val get_by_type : Term.t -> t -> int list
end

(***************************************************************************************)
(** Environments. *)

module Env : sig
  (** Where to print a constant with respect to its arguments. 
      [Infix] only makes sense for functions that have two explicit arguments.
      [Suffix] only makes sense for functions that have one explicit argument.
      [Prefix] is always valid, and is what is used by default. *)
  type pp_pos = Prefix | Infix | Suffix [@@deriving show]

  (** Some global variables require special formatting when pretty-printed. *)
  type pp_info =
    { symbol : string
          (** The symbol to use to print the constant. For instance we might want to 
              print [Coq.Init.Peano.plus] as [+]. *)
    ; implicit_args : int list
          (** The indices of the implicit arguments of the constant.
              Implicit arguments are not printed, and are always before explicit arguments.  
              For instance the polymorphic equality [eq : forall A : Type, A -> A -> Prop] 
              has an implicit argument at index [0]. *)
    ; position : pp_pos
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

  (** [union env1 env2] takes the union of [env1] and [env2].
      This assumes that the two environments contain the same information for the constants 
      that appear in both. *)
  val union : t -> t -> t

  (** An environment containing a few constants. Used for testing.
      We assume that the types of the constants are well-typed. *)
  val test_env : t

  (** [Env.add_constant name ty env] adds the constant [name] with type [ty] 
      to the environment [env]. *)
  val add_constant : Name.t -> Term.t -> ?pp:pp_info -> t -> t

  (** [default_pp_info symbol] prints [symbol] in prefix position with no implicit arguments. *)
  val default_pp_info : string -> pp_info
end

(***************************************************************************************)
(** Term utility functions. *)

module TermUtils : sig
  (** [lift k n t] adds [n] to every free variable in [t] that is at index at least [k].
      [n] can be negative. *)
  val lift : int -> int -> Term.t -> Term.t

  (** [lift_free n t] adds [n] to every free variable in [t]. 
      [n] can be negative. *)
  val lift_free : int -> Term.t -> Term.t

  (** [subst k u t] replaces every occurence of the free variable [k] by the term [u] 
      in the term [t]. *)
  val subst : int -> Term.t -> Term.t -> Term.t

  (** [free_vars t] computes the set of free variables in [t]. *)
  val free_vars : Term.t -> IntSet.t

  (** [constants t] computes the set of constants used in [t]. *)
  val constants : Term.t -> Name.Set.t

  (** [subterm ?context t sub] returns the subterm of [t] at path [sub] 
      together with its local context. The argument [context] gives the initial
      context that [t] lives in : by default it is [Context.empty].
      Raises [InvalidSubtermPath] if [sub] is not a valid path in [t]. *)
  val subterm : ?context:Context.t -> Term.t -> int list -> Context.t * Term.t
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
  val check : ?context:Context.t -> Env.t -> Term.t -> Term.t

  (** [typeof ?context env t] gets the type of the term [t]. 
      This assumes that [t] is well-typed, and is faster than [check env t]. *)
  val typeof : ?context:Context.t -> Env.t -> Term.t -> Term.t
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
    ?context:Context.t -> ?ty:Term.t -> Env.t -> (Term.t * Term.t) Gen.t

  (** [context env] generates a typing context in [env]. 
      This can be fed to [typed] to generate open terms. *)
  val context : Env.t -> Context.t Gen.t
end
