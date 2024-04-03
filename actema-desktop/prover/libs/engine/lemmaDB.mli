(** This module defines the lemma database. The database consists of :
    - A list of lemmas (name and formula). 
    - An environment containing the predicates & functions used in the lemmas. *)

type t

exception LemmaNotFound of string

(** Returns the environment of the database. *)
val env : t -> Fo.env

(** Returns all the lemmas contained in the database. *)
val all_lemmas : t -> (string * Fo.form) list

(** Create an empty database, with a given environment. *)
val empty : Fo.env -> t

(** Get a lemma by name. Raises [LemmaNotFound] if the lemma does not exist in the database. *)
val get : t -> string -> Fo.form

(** Add a lemma to the database. 
    We assume that the symbols of the lemma are contained in the database env. *)
val add : t -> string -> Fo.form -> t
