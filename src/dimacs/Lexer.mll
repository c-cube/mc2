(*  Copyright 2005 INRIA  *)
{
  open Parser
}

let number = ['1'-'9'] ['0'-'9']*

rule token = parse
  | eof                     { EOF }
  | "c" [^ '\n']* '\n'      { Lexing.new_line lexbuf; token lexbuf }
  | [' ' '\t' '\r']         { token lexbuf }
  | 'p'                     { P }
  | "cnf"                   { CNF }
  | '\n'                    { Lexing.new_line lexbuf; EOL }
  | '0'                     { ZERO }
  | '-'? number             { LIT (int_of_string (Lexing.lexeme lexbuf)) }
