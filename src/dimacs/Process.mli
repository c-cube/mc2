
(** {1 Main for dimacs} *)

open Mc2_core
open Solver_types

type 'a or_error = ('a, string) CCResult.t

val parse : Service.Registry.t -> string -> atom list list or_error

val solve : Solver.t -> Solver.res or_error

val process :
  ?gc:bool ->
  ?restarts:bool ->
  ?pp_model:bool ->
  ?check:bool ->
  ?time:float ->
  ?memory:float ->
  Solver.t ->
  atom list list ->
  unit or_error

