(* -------------------------------------------------------------------- *)
{
  open Utils
  open Parser

  module L = Location

  (* ------------------------------------------------------------------ *)
  let lex_error lexbuf msg =
    raise (Syntax.ParseError (Some (L.of_lexbuf lexbuf), Some msg))

  (* ------------------------------------------------------------------ *)
  let _keywords = [
    "true"  , TRUE  ;
    "exists", EXISTS;
    "false" , FALSE ;
    "forall", FORALL;
    "rec"   , REC   ;
  ]

  (* ------------------------------------------------------------------ *)
  let keywords =
    let table = Hashtbl.create 0 in
    List.iter (curry (Hashtbl.add table)) _keywords; table
}

let empty   = ""
let blank   = [' ' '\t' '\r']
let newline = '\n'
let upper   = ['A'-'Z']
let lower   = ['a'-'z']
let letter  = upper | lower
let digit   = ['0'-'9']
let uint    = digit+

let ichar = (letter | digit | '_' | '\'')
let ident = letter ichar*

(* -------------------------------------------------------------------- *)
rule main = parse
  | newline     { Lexing.new_line lexbuf; main lexbuf }
  | blank+      { main lexbuf }
  | ident as id { try Hashtbl.find keywords id with Not_found -> IDENT id }

  | "("   { LPAREN  }
  | ")"   { RPAREN  }
  | "&&"  { LAND    }
  | "||"  { LOR     }
  | "~"   { LNEG    }
  | "->"  { LARROW  }
  | "<->" { LRARROW }
  | "|-"  { PROOF   }
  | ","   { COMMA   }
  | "."   { DOT     }
  | ":"   { COLON   }
  | "::"  { DCOLON  }
  | ":="  { COLONEQ }
  | "&"   { AMP     }
  | "+"   { PLUS    }
  | "*"   { STAR    }

  | eof { EOF }

  |  _ as c { lex_error lexbuf (Printf.sprintf "illegal character: %c" c) }
