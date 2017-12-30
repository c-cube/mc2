  
(** {1 Trivial plugin for SAT} *)

open Mc2_core

val k_atom : (int -> atom) Service.Key.t

val plugin : Plugin.Factory.t
