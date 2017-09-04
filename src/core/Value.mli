
(** {1 Values} *)

(** A value belongs in models. Every term must eventually be assigned to
    a value. *)

open Solver_types

type t = value

val equal : t -> t -> bool
val hash : t -> int
val pp : t CCFormat.printer

val make : tc_value -> value_view -> t
(** Main construction for values *)
