
open Solver_types

type t = premise

val prefix : t -> string

val raw_steps : raw_premise_step list -> t
(** Hyper resolution/paramod, raw form
    precondition: list.length >= 2 *)

val raw_steps_or_simplify : raw_premise_step list -> t
(** If singleton list, simplify; else Raw_steps
    precondition: list not empty, first item is a clause *)

val steps : clause -> premise_step list -> t

val pp_raw_premise_step : raw_premise_step Fmt.printer
val pp_premise_step : premise_step Fmt.printer
val pp : t Fmt.printer
