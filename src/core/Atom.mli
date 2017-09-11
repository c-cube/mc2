
open Solver_types

type t = Solver_types.atom

val equal : t -> t -> bool
val compare : t -> t -> int

val same_term : t -> t -> bool (** same term, ignoring sign? *)

val is_pos : t -> bool (** Positive atom? *)
val neg : t -> t (** Negation *)
val abs : t -> t (** Positive version *)
val value : t -> term_assignment
val value_exn : t -> value
val value_bool : t -> bool option
val value_bool_exn : t -> bool

val mark : t -> unit (** Mark the atom as seen, using fields in the variable. *)
val marked : t -> bool (** Returns wether the atom has been marked as seen. *)
val unmark : t -> unit

val level : t -> int (** decision level of the variable *)
val reason : t -> reason option
val is_true : t -> bool (** True in current model? *)
val is_false : t -> bool
val is_undef : t -> bool
val has_value : t -> bool

val term : t -> term
val watched : t -> clause Vec.t

val pp : t CCFormat.printer (** nice printer *)
val debug : t CCFormat.printer (** very verbose printer *)

module Set : CCSet.S with type elt = atom
