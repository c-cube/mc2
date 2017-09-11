  
(** {1 Trivial plugin for SAT} *)

open Mc2_core
open Solver_types

val k_atom : (int -> atom) Service.Key.t

val plugin : Plugin.Factory.t
