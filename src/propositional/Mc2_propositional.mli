
(** {1 Propositional Literal} *)

open Mc2_core
open Solver_types

module F : Tseitin.S with type atom := atom
(** Formulas *)

val k_cnf : (?simplify:bool -> F.t -> atom list list) Service.Key.t
(** Service for computing CNF *)

val k_fresh : (unit -> atom) Service.Key.t
(** Service for making fresh terms *)

val plugin : Plugin.Factory.t
(** Plugin providing boolean terms and the {!cnf} service *)


