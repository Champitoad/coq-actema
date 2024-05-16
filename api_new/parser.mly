(*%{
  open Lang
  open Term

  exception ParsingError of string
%}

%token <string> IDENT (* A variable identifier. *)
%token <string> OPERATOR (* An infix or suffix operator. *)
%token <int> NAT

%token LPAREN RPAREN
%token LBRACE RBRACE
%token DOT SEMICOLON COMMA COLON
%token FUN
%token EXISTS
%token FORALL
%token PROP
%token TYPE
%token THIN_ARROW (* -> *)
%token FAT_ARROW (* => *)
%token EOF

%right THIN_ARROW FAT_ARROW

%type <Lang.Term.t> xprogram
%start xprogram

%%

xprogram:
  | t=xterm EOF { t } ;

xterm:
  | LPAREN t=xterm RPAREN { t }
  | FUN x=IDENT COLON ty=xterm FAT_ARROW body=xterm { mkLambda x ty body }
  | FORALL x=IDENT COLON ty=xterm FAT_ARROW body=xterm { mkProd x ty body }
  | t1=xterm THIN_ARROW t2=xterm { mkArrow t1 t2 }
  | f=xterm args=xterm* { mkApps f args }
  | ident *)