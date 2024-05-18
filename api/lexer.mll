(*{
  open Parser

  exception LexingError of string

  let lex_error msg =
    raise @@ LexingError msg

  let _keywords = 
  [ "forall", FORALL
  ; "exists", EXISTS
  ; "fun", FUN
  ; "Prop", PROP
  ; "Type", TYPE
  ]

  let keywords =
    let table = Hashtbl.create 0 in
    List.iter (curry (Hashtbl.add table)) _keywords; table
}

(****************************************************************************)

let empty   = ""
let blanks  = [' ' '\t']+
let newline = '\n' | '\r' | "\r\n"
let upper   = ['A'-'Z']
let lower   = ['a'-'z']
let letter  = upper | lower
let digit   = ['0'-'9']
let uint    = digit+

let ichar = (letter | digit | '_' | '\'' | '.')
let ident = letter ichar*
let nat   = digit+

(****************************************************************************)

rule main = parse
  | newline     { Lexing.new_line lexbuf; main lexbuf }
  | blanks      { main lexbuf }
  | ident as id { try Hashtbl.find keywords id with Not_found -> IDENT id }
  | nat as n    { NAT (int_of_string n) }

  | "("   { LPAREN     }
  | ")"   { RPAREN     }
  | "{"   { LBRACE     }
  | "}"   { RBRACE     }
  | "->"  { THIN_ARROW }
  | "=>"  { FAT_ARROW  }
  | ","   { COMMA      }
  | "."   { DOT        }
  | ";"   { SEMICOLON  }
  | ":"   { COLON      }

  | eof { EOF }

  |  _ as c { lex_error (Printf.sprintf "illegal character: %c" c) }
*)