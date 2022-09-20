module BiMap (S : Map.OrderedType) (T : Map.OrderedType) = struct
  module SMap = Map.Make(S)
  module TMap = Map.Make(T)

  type t = T.t SMap.t * S.t TMap.t


  let bindings (r, _) =
    SMap.bindings r

  let of_list xs =
    let r = xs |> List.to_seq |> SMap.of_seq in
    let l = xs |> List.map (fun (x, y) -> y, x) |> List.to_seq |> TMap.of_seq in
    (r, l)

  let keys (r, _) =
    SMap.bindings r |> Stdlib.List.split |> fst

  let values (r, _) =
    SMap.bindings r |> Stdlib.List.split |> snd
  
  let size (r, _) =
    r |> SMap.bindings |> List.length

  
  let empty =
    SMap.empty, TMap.empty
  
  let add k v (r, l) =
    if SMap.mem k r then (r, l)
    else (SMap.add k v r, TMap.add v k l)

  let replace k v (r, l) =
    SMap.add k v r, TMap.add v k l
  
  let remove k (r, l) =
    let v = SMap.find k r in
    SMap.remove k r, TMap.remove v l

  
  let find k (r, _) =
    SMap.find k r

  let find_opt k (r, _) =
    SMap.find_opt k r
  
  let dnif v (_, l) =
    TMap.find v l

  let dnif_opt v (_, l) =
    TMap.find_opt v l
end

module List = struct
  include Stdlib.List

  let nth_index n x l =
    let rec aux acc n x l =
      begin match l with
      | y :: l ->
          let n = if x = y then n - 1 else n in
          if n < 0 then acc
          else aux (acc + 1) n x l
      | [] -> raise Not_found
      end
    in aux 0 n x l
end
