
open Solver_types

(* Decisions & propagations *)
type t = assignment =
  | Assign_term of term
  | Assign_atom of atom

let of_term t = Assign_term t
let of_atom a = Assign_atom a

let dummy = of_term Term.dummy
