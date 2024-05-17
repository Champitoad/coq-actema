open Lang

type sitem = Sbound of Term.t | Sflex
type 'a eqns = ('a * 'a) list

module Subst = struct
  type subst = (Name.t * sitem) list

  let empty = []
  let is_empty subst = subst = []
  let aslist (s : subst) : _ list = s
  let oflist (s : _ list) : subst = s
  let fold = List.fold_left

  let rec get_tag ((n, i) as x : vname) (s : subst) =
    match s with
    | [] -> None
    | (m, tag) :: s when n = m ->
        if i = 0 then Some tag else get_tag (n, i - 1) s
    | _ :: s -> get_tag x s

  let flex (x : vname) (s : subst) = get_tag x s = Some Sflex

  let bound (x : vname) (s : subst) =
    match get_tag x s with Some (Sbound _) -> true | _ -> false

  exception UnboundVariable of vname * subst

  let fetch (x : vname) (s : subst) =
    match get_tag x s with
    | Some (Sbound e) -> e
    | _ -> raise (UnboundVariable (x, s))

  let rec add ((n, i) as x : vname) (e : expr) : subst -> subst = function
    | [] -> failwith "Subst.add [1]"
    | (m, t) :: s when n <> m -> (m, t) :: add x e s
    | (m, t) :: s when n = m && i > 0 -> (m, t) :: add (n, i - 1) e s
    | (m, Sflex) :: s when n = m && i = 0 -> (m, Sbound e) :: s
    | _ -> failwith "Subst.add [2]"

  let push m t s = (m, t) :: s
  let is_complete (s : subst) = List.for_all (fun (_, tag) -> tag <> Sflex) s

  let rec e_apply1 ((x, i) : name * int) (e : expr) (tg : expr) : expr =
    match tg with
    | EVar (y, j) when x = y && i = j -> e
    | EVar (y, j) when x = y && i < j -> EVar (y, j - 1)
    | EVar _ -> tg
    | EFun (f, args) -> EFun (f, List.map (e_apply1 (x, i) e) args)

  let rec f_apply1 ((x, i) : name * int) (e : expr) (f : form) : form =
    match f with
    | FTrue | FFalse -> f
    | FConn (lg, fs) -> FConn (lg, List.map (f_apply1 (x, i) e) fs)
    | FPred (name, args) -> FPred (name, List.map (e_apply1 (x, i) e) args)
    | FBind (bd, y, ty, f) ->
        FBind
          ( bd
          , y
          , ty
          , f_apply1 (x, i + if x = y then 1 else 0) (e_shift (y, i) e) f )

  let rec e_iter s i e =
    if i = 0
    then e
    else
      match s with
      | [] -> assert false
      | (x, Sbound e) :: s -> e_iter s (i - 1) (e_apply1 (x, 0) e e)
      | (_, _) :: s -> e_iter s (i - 1) e

  let rec f_iter s i f =
    if i = 0
    then f
    else
      match s with
      | [] -> assert false
      | (x, Sbound e) :: s -> f_iter s (i - 1) (f_apply1 (x, 0) e f)
      | (_, _) :: s -> f_iter s (i - 1) f

  let e_apply s e = e_iter s (List.length s) e
  let f_apply s f = f_iter s (List.length s) f

  let rec e_close s = function
    | EVar x -> begin
        try e_close s (fetch x s) with UnboundVariable _ -> EVar x
      end
    | EFun (f, es) -> EFun (f, List.map (e_close s) es)

  let close s =
    s
    |> List.map
         begin
           fun (x, tag) ->
             let tag =
               match tag with Sbound e -> Sbound (e_close s e) | _ -> tag
             in
             (x, tag)
         end

  let to_string =
    List.to_string ~sep:", " ~left:"{" ~right:"}" (fun (x, tag) ->
        match tag with
        | Sflex -> "Sflex(" ^ x ^ ")"
        | Sbound e -> "Sbound(" ^ x ^ ")")
end
