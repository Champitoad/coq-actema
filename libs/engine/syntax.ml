(* -------------------------------------------------------------------- *)
open Location

(* -------------------------------------------------------------------- *)
type symbol  = string
type psymbol = symbol loced

(* -------------------------------------------------------------------- *)
type pty_r =
  | PTUnit
  | PTOr  of pty * pty
  | PTAnd of pty * pty

and pty = pty_r loced

(* -------------------------------------------------------------------- *)
type pexpr_r =
  | PEUnit
  | PEOp   of psymbol * pexpr list
  | PEInj  of [`Left | `Right] * pexpr
  | PEPair of pexpr * pexpr

and pexpr = pexpr_r loced

(* -------------------------------------------------------------------- *)
type pform_r =
  | PFPred   of psymbol * pexpr list
  | PFCst    of bool
  | PFAnd    of pform * pform
  | PFOr     of pform * pform
  | PFNot    of pform
  | PFForall of (psymbol * pty option) * pform
  | PFExists of (psymbol * pty option) * pform

and pform = pform_r loced
