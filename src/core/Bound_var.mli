
open Solver_types

type t = bound_var

type term_view += private BVar of bound_var

val pp : t Fmt.printer
val pp_with_ty : t Fmt.printer

val k_bvar : (t -> term) Service.Key.t
(** Service for turning a bound-variable into a term *)

val plugin : Plugin.Factory.t
