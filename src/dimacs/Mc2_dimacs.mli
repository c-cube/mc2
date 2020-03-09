
(** {1 Main for dimacs} *)

(** This library provides a parser for DIMACS files, to represent
    SAT problems.

    http://www.satcompetition.org/2009/format-benchmarks2009.html
*)

open Mc2_core

module Plugin_sat = Plugin_sat

type 'a or_error = ('a, string) CCResult.t

val plugin : Plugin.Factory.t

val k_atom : (int -> atom) Service.Key.t
(** Key to build atoms *)

val parse : Service.Registry.t -> string -> atom list list or_error
(** Parse a file into a list of clauses.
    @param registry used to build atoms from integers, see {!k_atom} *)

val solve : Solver.t -> Solver.res or_error
(** Solve a problem *)

val process :
  ?gc:bool ->
  ?restarts:bool ->
  ?dot_proof:string ->
  ?pp_model:bool ->
  ?check:bool ->
  ?time:float ->
  ?memory:float ->
  ?progress:bool ->
  Solver.t ->
  atom list list ->
  unit or_error
(** Add clauses to solver, solve, and prints the results.
    @param check check proof/model
    @param progress print progress bar
    @param dot_proof file into which to print the proof
*)

