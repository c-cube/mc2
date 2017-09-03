
(** {1 Propositional Literal} *)

open Mc2_core
open Solver_types

type t = atom

val neg : t -> t
(** Negation of atomic formulas. *)

val pp : t CCFormat.printer
(** Print the given formula. *)

module F : Tseitin.S with type atom := t
(** Formulas *)

val k_cnf : (?simplify:bool -> F.t -> t list list) Service.Key.t
(** Service for computing CNF *)

val k_fresh : (unit -> t) Service.Key.t
(** Service for making fresh terms *)

val plugin : Plugin.Factory.t
(** Plugin providing boolean terms and the {!cnf} service *)


