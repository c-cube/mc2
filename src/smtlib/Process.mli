
(** {1 Process Statements} *)

open Mc2_core
open Solver_types

type 'a or_error = ('a, string) CCResult.t

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
  Solver.t ->
  Ast.statement ->
  unit or_error
(** Process the given statement.
    @raise Incorrect_model if model is not correct
*)

val parse : ?ctx:Ast.Ctx.t -> string -> Ast.statement list or_error
(** Parse the given file, type-check, etc.
    @raise Error in case the input is ill formed
    @raise Ill_typed if the input is ill typed *)

val parse_stdin : ?ctx:Ast.Ctx.t -> unit -> Ast.statement list or_error
(** Parse stdin, type-check, etc.
    @raise Error in case the input is ill formed
    @raise Ill_typed if the input is ill typed *)
