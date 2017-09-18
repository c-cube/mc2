
(** {1 Some builtins} *)

(** This plugin is always included automatically *)

open Solver_types

val k_true : term Service.Key.t (** Trivial boolean term *)
val k_false : term Service.Key.t (** Absurd boolean term *)

val plugin : Plugin.Factory.t
