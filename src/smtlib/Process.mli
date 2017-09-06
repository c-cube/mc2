
(** {1 Process Statements} *)

open Mc2_core
open Solver_types

type 'a or_error = ('a, string) CCResult.t

exception Incorrect_model
exception Out_of_time
exception Out_of_space

val conv_bool_term : Service.Registry.t -> Ast.term -> atom list list
(** Convert a boolean term into CNF *)

val p_check : bool ref
(** Check proofs and models? *)

val with_limits :
  time:float ->
  memory:float ->
  (unit -> 'a) ->
  'a
(** Perform computation [f ()] with limited amount of time and space.
    @param time limit, in seconds, measured with [Sys.time()]
    @param memory number of words in the heap
    @raise Out_of_time if out of time
    @raise Out_of_space if out of space
*)

val process_stmt :
  ?pp_cnf:bool ->
  ?dot_proof:string ->
  Solver.t ->
  Ast.statement ->
  unit or_error
(** Process the given statement.
    @raise Incorrect_model if model is not correct
*)

val setup_gc : unit -> unit
(** Change parameters of the GC *)
