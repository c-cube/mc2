
open Solver_types

type t = premise

val prefix : t -> string

val pp : t CCFormat.printer

val hyper_res : clause list -> t
