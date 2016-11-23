%{
  open Utils
  open Location
  open Syntax
%}

%token <Syntax.symbol> LIDENT
%token <Syntax.symbol> UIDENT

%token EXISTS
%token FORALL
%token TRUE
%token FALSE
%token EOF

%token COMMA LPAREN RPAREN LT GT
%token LAND LOR LNEG

%nonassoc COMMA LT GT

%left LOR
%left LAND
%left LNEG

%type <Syntax.pform> xform
%type <Syntax.pexpr> xexpr

%start xform xexpr
%%

(* -------------------------------------------------------------------- *)
xform:
| f=form EOF { f }

(* -------------------------------------------------------------------- *)
xexpr:
| e=expr EOF { e }

(* -------------------------------------------------------------------- *)
%inline lident: x=loc(LIDENT) { x }
%inline uident: x=loc(UIDENT) { x }

(* -------------------------------------------------------------------- *)
binding:
| x=lident { (x, None) }

(* -------------------------------------------------------------------- *)
expr_r:
| e=parens(expr_r)
    { e }

| parens(empty)
    { PEUnit }

| x=lident args=parens(plist1(expr, COMMA))?
    { PEOp (x, Option.default [] args) }

| e=parens(e1=expr COMMA e2=expr { (e1, e2) })
    { let e1, e2 = e in PEPair (e1, e2) }

| LT e=expr
    { PEInj (`Left, e) }

| e=expr GT
    { PEInj (`Right, e) }

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

| x=uident args=parens(plist1(expr, COMMA))?
    { PFPred (x, Option.default [] args) }

| f1=form LAND f2=form
    { PFAnd (f1, f2) }

| f1=form LOR f2=form
    { PFOr (f1, f2) }

| LNEG f=form
    { PFNot f }

| FORALL x=binding COMMA f=form
    { PFForall (x, f) }

| EXISTS x=binding COMMA f=form
    { PFForall (x, f) }

form:
| f=loc(form_r) { f }

(* -------------------------------------------------------------------- *)
%inline empty: | (* empty *) { () }

(* -------------------------------------------------------------------- *)
%inline loc(X):
| x=X {
    { pldesc = x;
      plloc  = Location.make $startpos $endpos;
    }
  }

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
