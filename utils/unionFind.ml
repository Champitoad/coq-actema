module type S = sig
  type elt
  type t

  val create : unit -> t
  val add : t -> elt -> unit
  val of_list : elt list -> t
  val domain : t -> elt list
  val find : t -> elt -> elt
  val union : t -> elt -> elt -> unit
  val equiv : t -> elt -> elt -> bool
  val is_representative : t -> elt -> bool
end

module Make (Elt : Hashtbl.HashedType) : S with type elt = Elt.t = struct
  module HT = Hashtbl.Make (Elt)

  type elt = Elt.t

  (** As an invariant [parent] and [rank] should contain the same keys. *)
  type t =
    { (* The direct parent (not the representative) of each element. *)
      parent : elt HT.t
    ; (* The rank of each element. This is an upper bound on the
         height of the subtree rooted at this element. It never decreases
         and only increases when performing unions. *)
      rank : int HT.t
    }

  let create () = { parent = HT.create 8; rank = HT.create 8 }

  let add uf elt =
    HT.add uf.parent elt elt;
    HT.add uf.rank elt 0

  let of_list elts =
    let uf = create () in
    List.iter (add uf) elts;
    uf

  let domain uf = uf.parent |> HT.to_seq_keys |> List.of_seq

  let rec find uf elt =
    let parent = HT.find uf.parent elt in
    if Elt.equal parent elt
    then elt
    else begin
      (* Recurse on the parent. *)
      let root = find uf parent in
      (* Path compression. We don't update the rank here,
         although the actual height of [elt] might decrease. *)
      HT.replace uf.parent elt root;
      root
    end

  let equiv uf x y = Elt.equal (find uf x) (find uf y)

  let union uf x y =
    (* Replace elements by roots. *)
    let x = find uf x in
    let y = find uf y in
    (* Make sure they are not already equal. *)
    if not @@ Elt.equal x y
    then begin
      (* Get the rank of x and y. *)
      let rx = HT.find uf.rank x in
      let ry = HT.find uf.rank y in
      if rx = ry
      then begin
        (* x becomes the parent of y. *)
        HT.replace uf.parent y x;
        HT.replace uf.rank x (rx + 1)
      end
      else if rx > ry
      then (* x becomes the parent of y. *)
        HT.replace uf.parent y x
      else (* y becomes the parent of x. *)
        HT.replace uf.parent x y
    end

  let is_representative uf elt =
    let root = find uf elt in
    Elt.equal elt root
end
