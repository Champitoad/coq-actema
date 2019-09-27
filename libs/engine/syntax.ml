(* -------------------------------------------------------------------- *)
open Location

(* -------------------------------------------------------------------- *)
type symbol  = string
type psymbol = symbol loced

(* -------------------------------------------------------------------- *)
type pform_r =
  | PFVar    of psymbol
  | PFCst    of bool
  | PFAnd    of pform * pform
  | PFOr     of pform * pform
  | PFImp    of pform * pform
  | PFEquiv  of pform * pform
  | PFNot    of pform

and pform = pform_r loced

(* -------------------------------------------------------------------- *)
type pgoal = psymbol list * pform
