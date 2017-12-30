
(** {1 SMTLib-2 Interface} *)

(** This library provides a parser, a type-checker, and a solver interface
    for processing SMTLib-2 problems.
*)

open Mc2_core

type 'a or_error = ('a, string) CCResult.t

module Ast = Ast

val parse : string -> Ast.statement list or_error

val parse_stdin : unit -> Ast.statement list or_error

val conv_bool_term : Service.Registry.t -> Ast.term -> atom list list
(** Convert a boolean term into CNF *)

val process_stmt :
  ?gc:bool ->
  ?restarts:bool ->
  ?pp_cnf:bool ->
  ?dot_proof:string ->
  ?pp_model:bool ->
  ?check:bool ->
  ?time:float ->
  ?memory:float ->
  ?progress:bool ->
  Solver.t ->
  Ast.statement ->
  unit or_error
(** Process the given statement.
    @raise Incorrect_model if model is not correct
*)
