/*  Copyright 2005 INRIA  */

%{
  open Mc2_core

  let lnum pos = pos.Lexing.pos_lnum
  let cnum pos = pos.Lexing.pos_cnum - pos.Lexing.pos_bol
  let pp_pos out (start,stop) =
    Format.fprintf out "(at %d:%d - %d:%d)"
      (lnum start) (cnum start) (lnum stop) (cnum stop)
%}

%token <int> LIT
%token ZERO
%token P CNF EOL EOF

%start file
%type <int list list> file

%%

/* DIMACS syntax */

prelude:
  | P CNF LIT LIT { () }
  | error
    {
      Util.errorf "expected prelude %a" pp_pos ($startpos,$endpos)
    }

file:
  | EOF                             { [] }
  | prelude EOL* l=separated_list(EOL*, clause) EOF { l }
  | error
    {
      Util.errorf "expected prelude then clause list %a"
        pp_pos ($startpos,$endpos)
    }

clause:
  | ZERO EOL        { [] }
  | LIT clause      { $1 :: $2 }
