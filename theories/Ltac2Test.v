From Ltac2 Require Import Ltac2 Printf.


Ltac2 myfunc (x : bool) (ys : int list) : unit := 
  if x then printf "x : true"
  else printf "x : false";
  List.iter (printf "-> %i") ys.
