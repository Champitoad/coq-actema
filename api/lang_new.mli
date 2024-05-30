(** This module defines the language used by the frontend & prover. 
    We call this the Actema language to distinguish it from the language used by Coq.
    It is the plugin which creates Actema terms (from Coq terms). *)

open Utils.Pervasive

(***************************************************************************************)
(** Free variables. *)

module FVarId : sig
  (** An abstract free variable identifier. 
      Generation a free variable is done via a [Context.t].
      The information about a free variable, such as its name and type, are held in a [Context.t].
      
      The [show] and [pp] functions are for debug purposes only. *)
  type t [@@deriving show]

  val equal : t -> t -> bool
  val compare : t -> t -> int

  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t
end

(***************************************************************************************)
(** Terms *)

module Term : sig
  (** This abstract type contains cached data. This is used to annotate terms, 
      and used by low-level functions for efficiency reasons. 
      This is small : you can think of it as an integer if you want. *)
  type cdata

  (** This is essentially the Calculus of Constructions.
      We use the "locally nameless" representation for binders : bound variables 
      are represented using de Bruijn indices, and free variables are represented using names.
      For more info see : "I am not a number, I am a free variable", McBride & McKinna.

      This is a private type : use the smart constructors provided below to build terms. *)
  type t = private
    (* [BVar n] is a local variable bound by a lambda abstraction or a dependent product.
       The integer [n] is a de Bruijn index, starting at 0.

       A BVar which escapes the last binder is called a "loose" BVar. Except for low-level
       functions, terms should contain no loose BVar. You can use [instantiate] to turn a BVar into
       an FVar. *)
    | BVar of int
    (* [FVar id] is a free variable. You can use [abstract] to turn an FVar into a BVar. *)
    | FVar of FVarId.t
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
    (* [App _ f [x1; ...; xn]] represents the application [f x1 ... xn].
       We maintain the invariant that [f] itself is not an application,
       and that the argument list is not empty. *)
    | App of cdata * t * t list
    (* [Lambda _ x ty body] represents the lambda abstraction [fun x : ty => body].
       The term [ty] is the type of [x], and [x] can appear as a BVar in [body]. *)
    | Lambda of cdata * Name.t option * t * t
    (* [Prod _ x A B] is the product [forall x : A, B].
       [A] is the type of [x], and [x] can appear as a BVar in [body].

       If the binder is [None], then [x] does not appear in the body and
       this is a non-dependent product. *)
    | Prod of cdata * Name.t option * t * t
  [@@deriving show]

  (** Smart constructor for [Term.BVar]. *)
  val mkBVar : int -> t

  (** Smart constructor for [Term.FVar]. *)
  val mkFVar : FVarId.t -> t

  (** Smart constructor for [Term.Cst]. *)
  val mkCst : Name.t -> t

  (** Smart constructor for [Term.Sort]. *)
  val mkSort : [ `Prop | `Type ] -> t

  (** Equivalent to [mkSort `Prop]. *)
  val mkProp : t

  (** Equivalent to [mkSort `Type]. *)
  val mkType : t

  (** Smart constructor for [Term.App], ensuring that the function is not an application.
      This computes the cached data. *)
  val mkApp : t -> t -> t

  (** Same as [mkApp] but with multiple arguments. 
      If the argument list is empty, simply returns the function. *)
  val mkApps : t -> t list -> t

  (** Smart constructor for [Term.Prod] in case the product is non-dependent.
      This computes the cached data. *)
  val mkArrow : t -> t -> t

  (** [mkArrows [t1; ...; tn]] constructs the arrow [t1 -> ... -> tn]. 
      It assumes that the list is nonempty (i.e. n >= 1). *)
  val mkArrows : t list -> t

  (** Smart constructor for [Term.Lambda]. This assumes that the body contains a loose [BVar 0],
      and does not perform any sort of shifting/instantiation/abstraction.
      This computes the cached data. *)
  val mkLambda : Name.t option -> t -> t -> t

  (** Smart constructor for [Term.Prod]. This assumes that the body contains a loose [BVar 0],
      and does not perform any sort of shifting/instantiation/abstraction.
      This computes the cached data. *)
  val mkProd : Name.t option -> t -> t -> t

  (** [lift n term] adds [n] to every loose BVar in [term].
      This is O(1) if [term] has no loose BVar. *)
  val lift : int -> t -> t

  (** [subst s term] replaces the loose [BVar 0] in [term] by [s],
      and lowers by [1] every other BVar of [term]. 
      This is O(1) if [term] has no loose BVar. *)
  val subst : t -> t -> t

  (** [instantiate fvar term] is equivalent to [subst (FVar fvar) term]. *)
  val instantiate : FVarId.t -> t -> t

  (** [abstract fvar term] replaces [fvar] by the loose [BVar 0] in [term]. *)
  val abstract : FVarId.t -> t -> t

  (** [alpha_equiv t1 t2] checks whether [t1] and [t2] are alpha-equivalent,
      i.e. are equal up to binder names. *)
  val alpha_equiv : t -> t -> bool

  (** [free_vars t] computes the list of free variables in [t]. *)
  val free_vars : t -> FVarId.t list

  (** [constants t] computes the list of constants used in [t]. *)
  val constants : t -> Name.t list
end

(***************************************************************************************)
(** Local context, which holds information about free variables. *)

module Context : sig
  (** The entry associated to a single free variable. *)
  type entry =
    { (* The user-facing name of the free variable. *)
      name : Name.t option
    ; (* The type of the free variable. *)
      type_ : Term.t
    }
  [@@deriving show]

  (** A local context contains the name and type of the free variables in a term.
        Conceptually it is a (name, ty)], but may be implemented more efficiently. *)
  type t [@@deriving show]

  (** The empty typing context. *)
  val empty : t

  (** [fresh_var ctx] generates a new free variable identifer that is fresh in [ctx],
      and returns the updated context. *)
  val fresh_fvar : t -> FVarId.t * t

  (** [size ctx] returns the number of entries in [ctx]. *)
  val size : t -> int

  (** [add fvar entry ctx] adds the free variable [fvar] with entry [entry] to the context [ctx]. *)
  val add : FVarId.t -> entry -> t -> t

  (** [add_fresh entry ctx] generates a new free variable [fvar] using [fresh_var ctx],
      bind [fvar] to [entry] using [add fvar entry ctx], and returns [fvar] with the new context. *)
  val add_fresh : entry -> t -> FVarId.t * t

  (** [find fvar ctx] retrieves the entry associated to [fvar] in [ctx]. *)
  val find : FVarId.t -> t -> entry option

  (** [remove fvar ctx] removes the binding associated to [fvar] from [ctx]. *)
  val remove : FVarId.t -> t -> t
end

(** [InvalidSubtermPath (t, sub)] indicates that the term [t] has no 
    subterm at path [sub]. *)
exception InvalidSubtermPath of Term.t * int list

(***************************************************************************************)
(** We define the names of a few Coq constants that are handled in a special way. *)

module Constants : sig
  (** A dummy name. This is used when translating Coq terms 
      that cannot be represented in Actema. *)
  val dummy : Name.t

  (** Coq's inductive [(=) : forall A : Type, A -> A -> Prop]. *)
  val eq : Name.t

  (** Coq's inductive [nat : Type]. *)
  val nat : Name.t

  (** Coq's inductive [list : Type -> Type]. *)
  val list : Name.t

  (** Coq's logical conjunction [and_ : Prop -> Prop -> Prop]. *)
  val and_ : Name.t

  (** Coq's logical disjunction [or_ : Prop -> Prop -> Prop]. *)
  val or_ : Name.t

  (** Coq's logical negation [not : Prop -> Prop]. *)
  val not : Name.t

  (** Coq's logical equivalence [equiv : Prop -> Prop -> Prop]. *)
  val equiv : Name.t

  (** Coq's inductive [ex : forall A : Type, (A -> Prop) -> Prop]. *)
  val ex : Name.t

  (** Coq's constructor [O : nat]. *)
  val zero : Name.t

  (** Coq's constructor [S : nat -> nat]. *)
  val succ : Name.t

  (** Coq's constant [add : nat -> nat -> nat]. *)
  val add : Name.t

  (** Coq's constant [mul : nat -> nat -> nat]. *)
  val mul : Name.t

  (** Coq's inductive [True : Prop]. *)
  val true_ : Name.t

  (** Coq's inductive [False : Prop]. *)
  val false_ : Name.t

  (** [is_logical_conn name] tests whether [name] corresponds to a logical connector. *)
  val is_logical_conn : Name.t -> bool
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

  (** [filter_args pp_info args] filters out the implicit arguments in [args]. *)
  val filter_args : pp_info -> 'a list -> 'a list
end

(***************************************************************************************)
(** Manipulating terms. *)

module TermUtils : sig
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

  (** [well_typed ?context env t] checks that [t] is well-typed. *)
  val well_typed : ?context:Context.t -> Env.t -> Term.t -> bool

  (** [subterm ?context t sub] returns the subterm of [t] at path [sub]
        together with its local context. The argument [context] gives the initial
        context that [t] lives in : by default it is [Context.empty].
        Raises [InvalidSubtermPath] if [sub] is not a valid path in [t]. *)
  val subterm : ?context:Context.t -> Term.t -> int list -> Context.t * Term.t
end

(** This module defines functions for generating arbitrary terms.
      These are used mainly for testing.

      The algorithm to generate typed terms is inspired by :
        Testing an Optimising Compiler by Generating Random Lambda Terms
        https://www.cse.chalmers.se/~russo/publications_files/AST2011.pdf *)
(*module TermGen : sig
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
*)
