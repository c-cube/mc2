
(** {1 Paramodulation Clause} *)

open Solver_types

type t = paramod_clause

val make : term -> term -> atom list -> premise -> t

val lhs : t -> term
val rhs : t -> term
val guard : t -> atom list
val premise : t -> premise

val to_clause : t -> clause
(** Turn the pclause to a clause. *)

val pp : t Fmt.printer
val debug : t Fmt.printer

