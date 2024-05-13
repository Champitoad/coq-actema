(** This module defines the language used by the frontend & prover. 
    We call this the Actema language to distinguish it from the language used by Coq.
    It is the which creates Actema terms (from Coq terms). *)

(***************************************************************************************)
(** Names *)

module Name : sig
  (** A name uniquely identifies a variable (local or global).
    
      It contains the variable name (string) and also a unique tag (int). 
      The tag is used as a unique identifier, i.e. no two variables share the same tag. 
      This is mainly for efficiency reasons, i.e. to avoid comparing potentially long strings,
      but it also makes implementing unification more convenient.
      
      It is important that we cannot access a variable's tag from outside this module. *)
  type t

  (** Get the string representation of a variable. 
      This does NOT include the variable's tag, i.e. different variables can yield the same string. *)
  val str : t -> string

  (** Create a variable with the given name and a fresh unique tag. *)
  val make : string -> t

  (** Compare variables, using the variable's tag. *)
  val compare : t -> t -> int

  (** Test for equality between variables, using the variable's tag. *)
  val equal : t -> t -> bool

  (** Maps with names as keys. *)
  module Map : Map.S with type key = t
end

(***************************************************************************************)
(** Terms *)

module Term : sig
  (** A grammar for a small dependently-typed language. *)
  type t =
    (* [Var v] is a local variable bound by a lambda abstraction or a dependent product. *)
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
    (* [Cst c] is a global constant. It's type can be found in the environment.
       Examples of constants could be :
       - [nat] the inductive type of natural numbers.
       - [add] the addition on natural numbers.
       - [list] the inductive type of polymorphic lists.
       - [cons] the second constructor of [list].
       - [h] where h is a hypothesis (i.e. a variable of Coq's named context).

       Notable constants used in Actema (see names.mli for a list) :
       - Logical connectives [and], [or], etc.
       - The existential quantifier [ex].
       - The type of propositions [Prop].
       - [Type] the equivalent of Coq's [Type u].

       Note that the Actema language cannot distinguish between universe levels :
       this means that some terms might unify in Actema but not in Coq.
       This is okay because Coq always checks we do the right thing. The alternative would
       be to work with a Type hierarchy in Actema, which seems like a painful effort
       for such little gain.
    *)
    | Cst of Name.t
end

(***************************************************************************************)
(** Environments. *)

module Env : sig
  (** Some variables require special formatting when pretty-printed. 
      This applies to global variables of course, but also to local variables. 

      For instance if a local variable ("x", 42) shadows another local variable ("x", 25),
      we might want to print ("x", 42) as "x0" or "x1" or something instead of simply "x". *)
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

  (** An environment contains all the information needed to :
      - Type check terms.
      - Pretty-print terms. *)
  type t =
    { globals : Term.t Name.Map.t  (** The type of each GLOBAL variable. *)
    ; locals : Term.t Name.Map.t  (** The type of each LOCAL variable. *)
    ; pp : pp_info Name.Map.t  (** The information needed to pretty-print *)
    }
end
