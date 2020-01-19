%{
  open Location
  open Syntax
%}

%token <Syntax.symbol> IDENT

%token LPAREN RPAREN
%token TRUE
%token EXISTS
%token FALSE
%token FORALL
%token REC
%token LARROW
%token LRARROW
%token EOF
%token PROOF

%token LAND LOR LNEG PLUS STAR
%token COLON COMMA DOT

%right    LARROW LRARROW
%nonassoc REC_prec
%left     LOR  PLUS
%left     LAND STAR
%left     LNEG

%type <Syntax.ptype> xtype
%type <Syntax.pexpr> xexpr
%type <Syntax.pform> xform
%type <Syntax.pgoal> xgoal

%start xtype
%start xexpr
%start xform
%start xgoal
%%

(* -------------------------------------------------------------------- *)
xtype:
| error
    { raise (ParseError (Some (Location.make $startpos $endpos), None)) }

| t=type_ EOF { t }

(* -------------------------------------------------------------------- *)
xexpr:
| error
    { raise (ParseError (Some (Location.make $startpos $endpos), None)) }

| e=expr EOF { e }

(* -------------------------------------------------------------------- *)
xform:
| error
   { raise (ParseError (Some (Location.make $startpos $endpos), None)) }

| f=form EOF { f }

(* -------------------------------------------------------------------- *)
xgoal:
| error
   { raise (ParseError (Some (Location.make $startpos $endpos), None)) }

| p=goal EOF { p }

(* -------------------------------------------------------------------- *)
%inline ident: x=loc(IDENT) { x }

tyident:
| x=ident COLON ty=type_ { (x, ty) }

(* -------------------------------------------------------------------- *)
type_r:
| t=parens(type_r)
    { t }

| parens(empty)
    { PTUnit }

| t1=type_ PLUS t2=type_
    { PTSum (t1, t2) }

| t1=type_ STAR t2=type_
    { PTProd (t1, t2) }

| REC x=ident DOT t=type_ %prec REC_prec
    { PTRec (x, t) }

type_:
| t=loc(type_r) { t }

(* -------------------------------------------------------------------- *)
expr_r:
| e=parens(expr_r)
    { e }

| x=ident
    { PEVar x }

| f=ident args=parens(plist0(expr, COMMA))
    { PEApp (f, args) }

expr:
| e=loc(expr_r) { e }

(* -------------------------------------------------------------------- *)
form_r:
| f=parens(form_r)
    { f }

| TRUE
   { PFCst true }

| FALSE
   { PFCst false }

| x=ident
    { PFVar x }

| f1=form LAND f2=form
    { PFAnd (f1, f2) }

| f1=form LOR f2=form
    { PFOr (f1, f2) }

| f1=form LARROW f2=form
    { PFImp (f1, f2) }

| f1=form LRARROW f2=form
    { PFEquiv (f1, f2) }

| LNEG f=form
    { PFNot f }

| FORALL xty=tyident DOT f=form
    { PFForall (xty, f) }

| EXISTS xty=tyident DOT f=form
    { PFExists (xty, f) }

form:
| f=loc(form_r) { f }

(* -------------------------------------------------------------------- *)
goal:
| ps=plist0(ident, COMMA) PROOF f=form
    { (ps, f) }

(* -------------------------------------------------------------------- *)
%inline loc(X):
| x=X {
    { pldesc = x;
      plloc  = Location.make $startpos $endpos;
    }
  }

(* -------------------------------------------------------------------- *)
%inline empty:
| (* empty *) { () }

(* -------------------------------------------------------------------- *)
%inline parens(X):
| LPAREN x=X RPAREN { x }

(* -------------------------------------------------------------------- *)
%inline plist0(X, S):
| aout=separated_list(S, X) { aout }

iplist1_r(X, S):
| x=X { [x] }
| xs=iplist1_r(X, S) S x=X { x :: xs }

%inline iplist1(X, S):
| xs=iplist1_r(X, S) { List.rev xs }

%inline plist1(X, S):
| aout=separated_nonempty_list(S, X) { aout }

%inline plist2(X, S):
| x=X S xs=plist1(X, S) { x :: xs }

%inline list2(X):
| x=X xs=X+ { x :: xs }
