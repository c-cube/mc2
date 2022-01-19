
(** {1 SMTLib-2 Interface} *)

(** This library provides a parser, a type-checker, and a solver interface
    for processing SMTLib-2 problems.
*)

open Mc2_core

module PA = Smtlib_utils.V_2_6.Ast
module Typecheck = Typecheck

type 'a or_error = ('a, string) CCResult.t

module Make(ARG : sig
    val solver : Solver.t
  end)
  : sig
  val parse : string -> PA.statement list or_error

  val parse_stdin : unit -> PA.statement list or_error

  val typecheck : PA.statement list -> Statement.t list or_error

  val process_stmt :
    ?gc:bool ->
    ?restarts:bool ->
    ?pp_cnf:bool ->
    ?pp_model:bool ->
    ?check:bool ->
    ?time:float ->
    ?memory:float ->
    ?progress:bool ->
    ?smtcomp:bool ->
    ?switch:Util.Switch.t ->
    Statement.t ->
    unit or_error
  (** Process the given statement. *)
end
