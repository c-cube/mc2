
open Solver_types

type t = premise

val prefix : t -> string

val pp : t CCFormat.printer

val hyper_res : clause list -> t
(** Hyper_res
    precondition: list.length >= 2 *)

val hyper_res_or_simplify : clause list -> t
(** If singleton list, simplify; else Hyper_res
    precondition: list not empty *)

val resolve : term -> clause -> clause -> t
(** Simple resolution step *)
