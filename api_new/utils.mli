(** This module implements Quickcheck-like generators that can fail. *)
module FGen : sig
  open QCheck2

  type 'a t

  (* Monadic interface. *)

  val return : 'a -> 'a t
  val fail : 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t

  (** Lift a generator from [Gen] to [FGen] *)
  val lift : 'a Gen.t -> 'a t

  (* Composing [FGen]s. *)

  val oneof : 'a t list -> 'a t
end
(*
    let return (x : 'a) : 'a t = Gen.return @@ Some x
  
    let fail : 'a t = Gen.return None
  
    let bind (x : 'a t) (f : 'a -> 'b t) : 'b t =
      Gen.bind x @@ fun x_opt ->
      match x_opt with None -> Gen.return None | Some x_content -> f x_content
  
    let 
  
    let oneof (xs : 'a t list) : 'a t = 
  
  end*)
