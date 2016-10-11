open Id

type term =
  | Atom of string
  | Conj of term list

type zipper =
  | Top
  | InConj of term list * zipper * term list

type location = Location of term * zipper

let all_locations t =
  let top t = Location (t, Top) in
  let rec aux t =
    match t with
      | Atom _ ->
	[top t]
      | Conj ts ->
	top t :: aux' [] ts
  and aux' left = function
    | [] ->
      []
    | t :: right ->
      List.map (fun (Location (u, z)) ->
	Location (u, InConj (left, z, right))
      )	(aux t)
      @ aux' (t :: left) right
  in
  aux t

let map t fatom fconj =
  let rec aux zipper t =
    let here = Location (t, zipper) in
    match t with
    | Atom s ->
      fatom here s
    | Conj ts ->
      fconj here (aux' zipper [] ts)
  and aux' zipper left = function
    | [] ->
      []
    | t :: right ->
      aux (InConj (left, zipper, right)) t
      :: aux' zipper (t :: left) right
  in
  aux Top t

let rec string_of_term = function
  | Atom s -> s
  | Conj ts -> string_of_conj ts

and string_of_conj ts =
  String.concat "/\\" (List.map string_of_term ts)

let rec string_of_zipper = function
  | Top ->
    "top"
  | InConj (ls, z, rs) ->
    string_of_conj ls
    ^ " | " ^ string_of_zipper z
    ^ " | " ^ string_of_conj rs

let string_of_location (Location (t, z)) =
  string_of_term t ^ " at " ^ string_of_zipper z

type formula = {
  identifier : Id.t;
  term       : term;
}

let mk =
  let c = ref 0 in
  fun term -> incr c; { identifier = Id !c; term }

let mk_atom a = mk (Atom a)

let mk_conj ts = mk (Conj ts)

let equivalent { term = t } { term = u } =
  t = u
