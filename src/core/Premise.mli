
open Solver_types

type t = premise

val prefix : t -> string

val pp : t CCFormat.printer

val hres : clause list -> t
(** Hyper resolution, raw form
    precondition: list.length >= 2 *)

val hres_or_simplify : clause list -> t
(** If singleton list, simplify; else Hyper_res
    precondition: list not empty *)

val hyper_res : clause -> (term * clause) list -> t
