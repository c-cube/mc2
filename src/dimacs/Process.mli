
(** {1 Main for dimacs} *)

open Mc2_core

type 'a or_error = ('a, string) CCResult.t

val parse : Service.Registry.t -> string -> atom list list or_error

val solve : Solver.t -> Solver.res or_error

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

