(* -------------------------------------------------------------------- *)
open Location

exception ParseError of Location.t option * string option

(* -------------------------------------------------------------------- *)
type symbol  = string
type psymbol = symbol loced

(* -------------------------------------------------------------------- *)
type ptype_r =
  | PTUnit
  | PTSum  of ptype * ptype
  | PTProd of ptype * ptype
  | PTRec  of psymbol * ptype

and ptype = ptype_r loced

(* -------------------------------------------------------------------- *)
type ptyident = psymbol * ptype

(* -------------------------------------------------------------------- *)
type pexpr_r =
  | PEVar of psymbol
  | PEApp of psymbol * pexpr list

and pexpr = pexpr_r loced

(* -------------------------------------------------------------------- *)
type pform_r =
  | PFVar    of psymbol
  | PFCst    of bool
  | PFAnd    of pform * pform
  | PFOr     of pform * pform
  | PFImp    of pform * pform
  | PFEquiv  of pform * pform
  | PFNot    of pform
  | PFForall of ptyident * pform
  | PFExists of ptyident * pform

and pform = pform_r loced

(* -------------------------------------------------------------------- *)
type pgoal = psymbol list * pform
