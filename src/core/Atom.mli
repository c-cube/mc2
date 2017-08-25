
type t = Solver_types.atom

val mark : t -> unit
(** Mark the atom as seen, using the 'seen' field in the variable. *)

val seen  : t -> bool
(** Returns wether the atom has been marked as seen. *)

val print : Format.formatter -> t -> unit
