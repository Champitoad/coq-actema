(* -------------------------------------------------------------------- *)
{
  open Utils
  open Parser

  module L = Location

  (* ------------------------------------------------------------------ *)
  exception LexicalError of L.t option * string

  (* ------------------------------------------------------------------ *)
  let lex_error lexbuf msg =
    raise (LexicalError (Some (L.of_lexbuf lexbuf), msg))

  (* ------------------------------------------------------------------ *)
  let _keywords = [
    "true"  , TRUE  ;
    "false" , FALSE ;
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

let ichar  = (letter | digit | '_' | '\'')
let uident = upper ichar*

(* -------------------------------------------------------------------- *)
rule main = parse
  | newline      { Lexing.new_line lexbuf; main lexbuf }
  | blank+       { main lexbuf }
  | uident as id { try Hashtbl.find keywords id with Not_found -> UIDENT id }

  | "("   { LPAREN  }
  | ")"   { RPAREN  }
  | "&&"  { LAND    }
  | "||"  { LOR     }
  | "~"   { LNEG    }
  | "->"  { LARROW  }
  | "<->" { LRARROW }
  | "|-"  { PROOF   }
  | ","   { COMMA   }

  | eof { EOF }

  |  _ as c { lex_error lexbuf (Printf.sprintf "illegal character: %c" c) }
