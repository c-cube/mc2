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
%token P CNF EOF

%start file
%type <int list list> file

%%

/* DIMACS syntax */

prelude:
  | P CNF LIT LIT { () }
  | error
    {
      Error.errorf "expected prelude %a" pp_pos ($startpos,$endpos)
    }

clauses:
  | l=clause* { l }
  | error
    {
      Error.errorf "expected list of clauses %a"
        pp_pos ($startpos,$endpos)
    }

file:
  | prelude l=clauses EOF { l }

clause:
  | l=LIT+ ZERO { l }
