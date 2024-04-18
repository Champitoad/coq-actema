(** This module defines the storage of actema proofs on disk.
    Actema proofs are stored in a local folder, each proof in a separate file.
    
    The name of the file is computed from the actema proof. It could
    be a simple string chosen by the user each time they invoke the actema tactic, 
    but then this would require an intractable amount of name management from the user.

    The simple solution that we choose is to add in the identifier the local
    proof context, that is (a hash of) the hypotheses and conclusion at the
    point where the action is performed. Adding the global environment would be
    too much, since the identifier would break as soon as a new constant is
    added/removed earlier in the development (whether or not it is involved in
    the action).

    One could imagine a more elaborate system where actions in the same local
    context but in different modules/sections/proofs have different identifiers,
    but for now we dispense from such complexity (maybe experience will prove
    that it is necessary in the future). *)
open Api

(** A trace of actema actions. *)
type proof = (int * Logic.action) list

(** The path to the folder where we store proofs. *)
val proofs_folder : unit -> string

(** Save a proof to disk. *)
val save_proof : Logic.aident -> proof -> unit

(** Load a proof from disk. *)
val load_proof : Logic.aident -> proof option
