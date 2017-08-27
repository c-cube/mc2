
type t = Solver_types.atom

val mark : t -> unit
(** Mark the atom as seen, using the 'seen' field in the variable. *)

val seen  : t -> bool
(** Returns wether the atom has been marked as seen. *)

val equal : t -> t -> bool

val compare : t -> t -> int

val pp : t CCFormat.printer
