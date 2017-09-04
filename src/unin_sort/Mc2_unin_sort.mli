
(** {1 Uninterpreted Functions and Types} *)

open Mc2_core
open Solver_types

val k_decl_sort : (ID.t -> int -> unit) Service.Key.t
(** Declare a uninterpreted sort *)

val k_make : (ID.t -> Type.t list -> Type.t) Service.Key.t
(** Build an instance of an uninterpreted sort *)

val k_eq : (term -> term -> term) Service.Key.t
(** Equality between terms of unintepreted sorts *)

val plugin : Plugin.Factory.t
