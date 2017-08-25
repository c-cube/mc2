
type term = Solver_types.term
type atom = Solver_types.atom

type t = Solver_types.assignment

val of_term : term -> t
val of_atom : atom -> t
(** Constructors and destructors *)

