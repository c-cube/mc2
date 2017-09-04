
(** {1 Some builtins} *)

(** This plugin is always included automatically *)

open Solver_types

val k_true : term Service.Key.t
(** Trivial boolean term (and its negation) *)

val plugin : Plugin.Factory.t
