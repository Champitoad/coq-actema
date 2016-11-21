(* -------------------------------------------------------------------- *)
module List   = BatList
module Map    = BatMap
module Option = BatOption

(* --------------------------------------------------------------------- *)
let curry   f (x, y) = f x y
let uncurry f x y = f (x, y)
