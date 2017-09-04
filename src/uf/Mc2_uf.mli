
(** {1 Uninterpreted Functions and Constants} *)

open Mc2_core
open Solver_types

val k_app : (ID.t -> term list -> term) Service.Key.t
(** Service for applying a constant to some arguments.
    Arguments are:
    - The head function symbol
    - the list of arguments
*)

val k_const : (ID.t -> term) Service.Key.t
(** Service for turning a constant into a term *)

val k_decl : (ID.t -> Type.t list -> Type.t -> unit) Service.Key.t
(** Service for declaring an uninterpreted symbol *)

val plugin : Plugin.Factory.t
