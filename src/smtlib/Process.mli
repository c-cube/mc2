
(** {1 Process Statements} *)

open Mc2_core
open Solver_types

type 'a or_error = ('a, string) CCResult.t

exception Incorrect_model

val conv_bool_term : Service.Registry.t -> Ast.term -> atom list list
(** Convert a boolean term into CNF *)

val p_check : bool ref
(** Check proofs and models? *)

val process_stmt :
  ?gc:bool ->
  ?restarts:bool ->
  ?pp_cnf:bool ->
  ?dot_proof:string ->
  Solver.t ->
  Ast.statement ->
  unit or_error
(** Process the given statement.
    @raise Incorrect_model if model is not correct
*)
