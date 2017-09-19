
open Solver_types

type t = premise

val prefix : t -> string

val pp : t CCFormat.printer

val empty_paramod : paramod_info

val hres : ?paramod:paramod_info -> clause list -> t
(** Hyper resolution, raw form
    precondition: list.length >= 2 *)

val hres_or_simplify : ?paramod:paramod_info -> clause list -> t
(** If singleton list, simplify; else Hyper_res
    precondition: list not empty *)

val hyper_res : ?paramod:paramod_info -> clause -> (term * clause) list -> t
